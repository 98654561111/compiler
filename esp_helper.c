/* esp_helper.c -- user-space ESP for Taiwan Mobile VoLTE (PLMN 46697)
 *
 * Why this exists
 * --------------
 * The kernel on this ROM (android15-6.6) cannot produce an ESP transport-mode
 * packet whose payload contains a complete inner IP packet:
 *
 *   - esp6_output_head() only prepends the ESP header; there is no code path
 *     that builds an inner IPv6 header, and inner_template no longer exists.
 *   - The network only accepts mod=trans (mod=tunnel -> 403 Forbidden).
 *
 * So the kernel's ESP output is unusable for this P-CSCF.  This helper builds
 * and sends the ESP packet in user space, bypassing the kernel entirely.
 *
 * Modes
 * -----
 *   esp_helper --send <sip_file> <ue> <peer> <spi_out> <auth_key_hex> <src_port> <dst_port>
 *       Reads a SIP message from <sip_file>, builds a complete ESP transport-mode
 *       packet (outer IPv6 | ESP hdr | inner IPv6 | inner UDP | SIP | pad | trailer | ICV)
 *       and sends it via a raw socket.  Prints "ok" on success.
 *
 *   esp_helper --recv <ue> <peer> <spi_in> <auth_key_hex> <out_file> <timeout_sec>
 *       Listens on a raw socket for ESP packets addressed to <ue>, verifies the
 *       ICV, extracts the inner SIP message, and writes it to <out_file>.
 *       Runs until a packet is received or <timeout_sec> seconds elapse.
 *
 *   esp_helper --probe <ue> <peer>
 *       Sends a single ICMPv6 echo request to verify connectivity.
 *
 * Cipher: ecb(cipher_null) -- the network negotiates ealg=null, so the payload
 * is plaintext and no encryption is needed.  Auth: hmac(md5) truncated to 96 bits.
 *
 * Communication with the app
 * -------------------------
 *   The app writes the SIP message to a file and invokes --send.
 *   A background --recv process captures the 200 OK and writes it to a file.
 *   The app polls the response file.
 *
 * Build
 * -----
 *   aarch64-linux-gnu-gcc -O2 -Wall -Wextra -static esp_helper.c -o esp_helper
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/ip6.h>
#include <netinet/icmp6.h>
#include <arpa/inet.h>
#include <linux/if_packet.h>
#include <net/if.h>
#include <time.h>

/* AF_INET6, IPPROTO_ESP, IPPROTO_UDP, IPPROTO_IPV6 are already defined
 * by the system headers (netinet/in.h) on Linux.  Do not redefine them. */

/* ---- MD5 (RFC 1321) ---- */

static const uint32_t md5_k[64] = {
    0xd76aa478,0xe8c7b756,0x242070db,0xc1bdceee,0xf57c0faf,0x4787c62a,
    0xa8304613,0xfd469501,0x698098d8,0x8b44f7af,0xffff5bb1,0x895cd7be,
    0x6b901122,0xfd987193,0xa679438e,0x49b40821,0xf61e2562,0xc040b340,
    0x265e5a51,0xe9b6c7aa,0xd62f105d,0x02441453,0xd8a1e681,0xe7d3fbc8,
    0x21e1cde6,0xc33707d6,0xf4d50d87,0x455a14ed,0xa9e3e905,0xfcefa3f8,
    0x676f02d9,0x8d2a4c8a,0xfffa3942,0x8771f681,0x6d9d6122,0xfde5380c,
    0xa4beea44,0x4bdecfa9,0xf6bb4b60,0xbebfbc70,0x289b7ec6,0xeaa127fa,
    0xd4ef3085,0x04881d05,0xd9d4d039,0xe6db99e5,0x1fa27cf8,0xc4ac5665,
    0xf4292244,0x432aff97,0xab9423a7,0xfc93a039,0x655b59c3,0x8f0ccc92,
    0xffeff47d,0x85845dd1,0x6fa87e4f,0xfe2ce6e0,0xa3014314,0x4e0811a1,
    0xf7537e82,0xbd3af235,0x2ad7d2bb,0xeb86d391
};

static const uint32_t md5_s[64] = {
    7,12,17,22,7,12,17,22,7,12,17,22,7,12,17,22,
    5,9,14,20,5,9,14,20,5,9,14,20,5,9,14,20,
    4,11,16,23,4,11,16,23,4,11,16,23,4,11,16,23,
    6,10,15,21,6,10,15,21,6,10,15,21,6,10,15,21
};

static const uint32_t md5_r[64] = {
    0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
    1,6,11,0,5,10,15,4,9,14,3,8,13,2,7,12,
    5,8,11,14,1,4,7,10,13,0,3,6,9,12,15,2,
    0,7,14,5,12,3,10,1,8,15,6,13,4,11,2,9
};

static void md5_transform(uint32_t state[4], const unsigned char block[64]) {
    uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
    uint32_t x[16];
    for (int i = 0; i < 16; i++)
        x[i] = (uint32_t)block[i*4] | ((uint32_t)block[i*4+1] << 8) |
               ((uint32_t)block[i*4+2] << 16) | ((uint32_t)block[i*4+3] << 24);

    for (int i = 0; i < 64; i++) {
        uint32_t f, g;
        if (i < 16) { f = (b & c) | (~b & d); g = i; }
        else if (i < 32) { f = (d & b) | (~d & c); g = (5*i + 1) % 16; }
        else if (i < 48) { f = b ^ c ^ d; g = (3*i + 5) % 16; }
        else { f = c ^ (b | ~d); g = (7*i) % 16; }
        uint32_t temp = d;
        d = c;
        c = b;
        b = b + ((a + f + md5_k[i] + x[g]) << md5_s[i] |
                   (a + f + md5_k[i] + x[g]) >> (32 - md5_s[i]));
        a = temp;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
}

static void md5(const unsigned char *msg, size_t len, unsigned char out[16]) {
    uint32_t state[4] = {0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476};
    size_t i;
    unsigned char buf[64];
    size_t total = len;

    /* Process full 64-byte blocks */
    for (i = 0; i + 64 <= len; i += 64)
        md5_transform(state, msg + i);

    /* Pad the remainder */
    size_t rem = len % 64;
    memcpy(buf, msg + i, rem);
    buf[rem] = 0x80;
    memset(buf + rem + 1, 0, 64 - rem - 1);
    if (rem >= 56) {
        md5_transform(state, buf);
        memset(buf, 0, 64);
    }
    /* Append length in bits (little-endian) */
    uint64_t bitlen = (uint64_t)total * 8;
    for (int j = 0; j < 8; j++)
        buf[56 + j] = (unsigned char)((bitlen >> (j * 8)) & 0xff);
    md5_transform(state, buf);

    for (int j = 0; j < 4; j++) {
        out[j*4]   = (unsigned char)(state[j] & 0xff);
        out[j*4+1] = (unsigned char)((state[j] >> 8) & 0xff);
        out[j*4+2] = (unsigned char)((state[j] >> 16) & 0xff);
        out[j*4+3] = (unsigned char)((state[j] >> 24) & 0xff);
    }
}

static void hmac_md5(const unsigned char *key, size_t keylen,
                     const unsigned char *msg, size_t msglen,
                     unsigned char out[16]) {
    unsigned char k[64];
    memset(k, 0, 64);
    if (keylen > 64) {
        md5(key, keylen, k);
    } else {
        memcpy(k, key, keylen);
    }

    unsigned char inner[64], outer[64];
    for (int i = 0; i < 64; i++) {
        inner[i] = k[i] ^ 0x36;
        outer[i] = k[i] ^ 0x5c;
    }

    /* inner hash: MD5(inner_pad || message) */
    /* Build the full inner input */
    size_t inner_len = 64 + msglen;
    unsigned char *inner_input = malloc(inner_len);
    memcpy(inner_input, inner, 64);
    memcpy(inner_input + 64, msg, msglen);
    unsigned char inner_hash[16];
    md5(inner_input, inner_len, inner_hash);
    free(inner_input);

    /* outer hash: MD5(outer_pad || inner_hash) */
    unsigned char outer_input[80];
    memcpy(outer_input, outer, 64);
    memcpy(outer_input + 64, inner_hash, 16);
    md5(outer_input, 80, out);
}

/* ---- helpers ---- */

static int hex2bin(const char *hex, unsigned char *out, size_t outlen) {
    for (size_t i = 0; i < outlen; i++) {
        unsigned int v;
        if (sscanf(hex + i * 2, "%2x", &v) != 1) return -1;
        out[i] = (unsigned char)v;
    }
    return 0;
}

static void build_ipv6_header(unsigned char *buf, const struct in6_addr *src,
                              const struct in6_addr *dst, uint16_t payload_len,
                              uint8_t next_header) {
    buf[0] = 0x60;  /* version 6 */
    buf[1] = 0;
    buf[2] = (payload_len >> 8) & 0xff;
    buf[3] = payload_len & 0xff;
    buf[4] = 0;     /* flow label hi */
    buf[5] = 0;     /* flow label mid */
    buf[6] = next_header;
    buf[7] = 64;    /* hop limit */
    memcpy(buf + 8, src->s6_addr, 16);
    memcpy(buf + 24, dst->s6_addr, 16);
}

static void build_udp_header(unsigned char *buf, uint16_t src_port,
                             uint16_t dst_port, uint16_t len, uint16_t cksum) {
    buf[0] = (src_port >> 8) & 0xff;
    buf[1] = src_port & 0xff;
    buf[2] = (dst_port >> 8) & 0xff;
    buf[3] = dst_port & 0xff;
    buf[4] = (len >> 8) & 0xff;
    buf[5] = len & 0xff;
    buf[6] = (cksum >> 8) & 0xff;
    buf[7] = cksum & 0xff;
}

static uint16_t udp_checksum(const struct in6_addr *src, const struct in6_addr *dst,
                             const unsigned char *udp_hdr, size_t udp_len,
                             const unsigned char *payload, size_t payload_len) {
    /* IPv6 pseudo-header + UDP header + payload */
    size_t total = 40 + udp_len + payload_len;
    unsigned char *buf = calloc(total, 1);
    memcpy(buf, src->s6_addr, 16);
    memcpy(buf + 16, dst->s6_addr, 16);
    /* upper-layer length (32-bit) */
    buf[32] = (udp_len + payload_len) >> 24;
    buf[33] = ((udp_len + payload_len) >> 16) & 0xff;
    buf[34] = ((udp_len + payload_len) >> 8) & 0xff;
    buf[35] = (udp_len + payload_len) & 0xff;
    /* next header = 17 (UDP) */
    buf[39] = 17;
    /* UDP header */
    memcpy(buf + 40, udp_hdr, 8);
    /* payload */
    memcpy(buf + 48, payload, payload_len);

    /* sum all 16-bit words */
    uint32_t sum = 0;
    for (size_t i = 0; i + 1 < total; i += 2) {
        sum += (buf[i] << 8) | buf[i + 1];
    }
    if (total % 2) {
        sum += buf[total - 1] << 8;
    }
    while (sum >> 16) {
        sum = (sum & 0xffff) + (sum >> 16);
    }
    uint16_t cks = (~sum) & 0xffff;
    if (cks == 0) cks = 0xffff;
    free(buf);
    return cks;
}

/* ---- ESP send ---- */

static int do_send(const char *sip_file, const char *ue_str, const char *peer_str,
                   const char *spi_str, const char *key_hex,
                   const char *src_port_str, const char *dst_port_str) {
    /* Read SIP message */
    FILE *f = fopen(sip_file, "rb");
    if (!f) { perror("fopen sip_file"); return 1; }
    fseek(f, 0, SEEK_END);
    long sip_len = ftell(f);
    fseek(f, 0, SEEK_SET);
    unsigned char *sip_msg = malloc(sip_len + 1);
    if (fread(sip_msg, 1, sip_len, f) != (size_t)sip_len) {
        perror("fread");
        fclose(f);
        return 1;
    }
    fclose(f);
    sip_msg[sip_len] = '\0';

    struct in6_addr ue, peer;
    if (inet_pton(AF_INET6, ue_str, &ue) != 1 ||
        inet_pton(AF_INET6, peer_str, &peer) != 1) {
        fprintf(stderr, "bad address\n");
        return 1;
    }

    uint32_t spi = (uint32_t)strtoul(spi_str, NULL, 0);
    uint16_t src_port = (uint16_t)atoi(src_port_str);
    uint16_t dst_port = (uint16_t)atoi(dst_port_str);

    unsigned char auth_key[16];
    if (hex2bin(key_hex, auth_key, 16) != 0) {
        fprintf(stderr, "bad auth key\n");
        return 1;
    }

    /* Build inner packet: IPv6(40) + UDP(8) + SIP */
    size_t inner_len = 40 + 8 + sip_len;
    unsigned char *inner = calloc(inner_len, 1);
    build_ipv6_header(inner, &ue, &peer, 8 + sip_len, IPPROTO_UDP);
    build_udp_header(inner + 40, src_port, dst_port, 8 + sip_len, 0);
    memcpy(inner + 48, sip_msg, sip_len);
    /* UDP checksum */
    uint16_t cksum = udp_checksum(&ue, &peer, inner + 40, 8, sip_msg, sip_len);
    inner[46] = (cksum >> 8) & 0xff;
    inner[47] = cksum & 0xff;

    /* ESP padding: align to 4 bytes, then 2-byte trailer */
    size_t pad_len = (4 - (inner_len % 4)) % 4;
    /* ensure at least 2 bytes for trailer */
    if (pad_len < 2) pad_len += 4;
    size_t trailer_len = 2;  /* padlen + nexthdr */
    size_t esp_payload_len = inner_len + pad_len + trailer_len;
    size_t total_len = 40 + 8 + esp_payload_len + 12;  /* IPv6 + ESP hdr + payload + ICV */

    unsigned char *packet = calloc(total_len, 1);

    /* Outer IPv6 header */
    build_ipv6_header(packet, &ue, &peer, 8 + esp_payload_len, IPPROTO_ESP);

    /* ESP header */
    uint32_t *esp_hdr = (uint32_t *)(packet + 40);
    esp_hdr[0] = htonl(spi);
    esp_hdr[1] = htonl(1);  /* seq = 1 */

    /* ESP payload: inner + padding + trailer */
    unsigned char *esp_payload = packet + 48;
    memcpy(esp_payload, inner, inner_len);
    memset(esp_payload + inner_len, 0, pad_len);
    esp_payload[inner_len + pad_len] = (unsigned char)pad_len;
    esp_payload[inner_len + pad_len + 1] = 41;  /* nexthdr = IPv6 (41) */

    /* ICV: HMAC-MD5-96 over SPI || seq || esp_payload */
    size_t icv_input_len = 8 + esp_payload_len;
    unsigned char *icv_input = malloc(icv_input_len);
    memcpy(icv_input, packet + 40, 8);  /* SPI + seq */
    memcpy(icv_input + 8, esp_payload, esp_payload_len);
    unsigned char icv[16];
    hmac_md5(auth_key, 16, icv_input, icv_input_len, icv);
    free(icv_input);

    /* Append ICV (first 12 bytes) */
    memcpy(packet + 48 + esp_payload_len, icv, 12);

    /* Send via raw socket */
    int sock = socket(AF_INET6, SOCK_RAW, IPPROTO_RAW);
    if (sock < 0) { perror("socket"); return 1; }

    /* Bind to interface */
    /* Find interface index */
    struct ifreq ifr;
    memset(&ifr, 0, sizeof(ifr));
    /* Try common IMS interface names */
    const char *ifaces[] = {"rmnet1", "rmnet0", NULL};
    for (int i = 0; ifaces[i]; i++) {
        strncpy(ifr.ifr_name, ifaces[i], IFNAMSIZ - 1);
        if (setsockopt(sock, SOL_SOCKET, SO_BINDTODEVICE, ifr.ifr_name, strlen(ifr.ifr_name)) == 0) {
            fprintf(stderr, "bound to %s\n", ifr.ifr_name);
            break;
        }
    }

    struct sockaddr_in6 dst;
    memset(&dst, 0, sizeof(dst));
    dst.sin6_family = AF_INET6;
    dst.sin6_addr = peer;
    dst.sin6_port = 0;

    ssize_t sent = sendto(sock, packet, total_len, 0,
                          (struct sockaddr *)&dst, sizeof(dst));
    if (sent < 0) {
        perror("sendto");
        close(sock);
        return 1;
    }
    fprintf(stderr, "sent %zd bytes (inner=%zu, esp_payload=%zu, total=%zu)\n",
            sent, inner_len, esp_payload_len, total_len);

    close(sock);
    free(inner);
    free(sip_msg);
    free(packet);
    printf("ok\n");
    return 0;
}

/* ---- ESP recv ---- */

static int do_recv(const char *ue_str, const char *peer_str,
                   const char *spi_str, const char *key_hex,
                   const char *out_file, int timeout_sec) {
    struct in6_addr ue, peer;
    if (inet_pton(AF_INET6, ue_str, &ue) != 1 ||
        inet_pton(AF_INET6, peer_str, &peer) != 1) {
        fprintf(stderr, "bad address\n");
        return 1;
    }
    uint32_t spi = (uint32_t)strtoul(spi_str, NULL, 0);
    unsigned char auth_key[16];
    if (hex2bin(key_hex, auth_key, 16) != 0) {
        fprintf(stderr, "bad auth key\n");
        return 1;
    }

    int sock = socket(AF_INET6, SOCK_RAW, IPPROTO_ESP);
    if (sock < 0) { perror("socket"); return 1; }

    /* Bind to interface */
    const char *ifaces[] = {"rmnet1", "rmnet0", NULL};
    struct ifreq ifr;
    for (int i = 0; ifaces[i]; i++) {
        memset(&ifr, 0, sizeof(ifr));
        strncpy(ifr.ifr_name, ifaces[i], IFNAMSIZ - 1);
        if (setsockopt(sock, SOL_SOCKET, SO_BINDTODEVICE, ifr.ifr_name, strlen(ifr.ifr_name)) == 0) {
            fprintf(stderr, "recv bound to %s\n", ifr.ifr_name);
            break;
        }
    }

    time_t deadline = time(NULL) + timeout_sec;
    while (time(NULL) < deadline) {
        struct pollfd pfd = { .fd = sock, .events = POLLIN };
        int remaining = (int)(deadline - time(NULL));
        if (remaining <= 0) break;
        int r = poll(&pfd, 1, remaining * 1000);
        if (r <= 0) continue;

        unsigned char buf[4096];
        struct sockaddr_in6 src;
        socklen_t srclen = sizeof(src);
        ssize_t n = recvfrom(sock, buf, sizeof(buf), 0,
                             (struct sockaddr *)&src, &srclen);
        if (n < 8 + 12) continue;  /* too short */

        uint32_t pkt_spi = ntohl(*(uint32_t *)buf);
        if (pkt_spi != spi) continue;

        uint32_t seq = ntohl(*(uint32_t *)(buf + 4));
        size_t esp_len = n;
        size_t payload_len = esp_len - 8 - 12;
        unsigned char *payload = buf + 8;
        unsigned char *icv = buf + 8 + payload_len;

        /* Verify ICV */
        size_t icv_input_len = 8 + payload_len;
        unsigned char *icv_input = malloc(icv_input_len);
        memcpy(icv_input, buf, 8);
        memcpy(icv_input + 8, payload, payload_len);
        unsigned char calc_icv[16];
        hmac_md5(auth_key, 16, icv_input, icv_input_len, calc_icv);
        free(icv_input);

        if (memcmp(calc_icv, icv, 12) != 0) {
            fprintf(stderr, "ICV mismatch, skipping\n");
            continue;
        }

        /* Extract inner packet (cipher_null = plaintext) */
        unsigned char padlen = payload[payload_len - 2];
        unsigned char nexthdr = payload[payload_len - 1];
        size_t inner_len = payload_len - padlen - 2;

        /* Parse inner IPv6 + UDP */
        if (inner_len < 48) continue;
        if ((payload[0] >> 4) != 6) continue;  /* not IPv6 */

        /* inner UDP header at offset 40 */
        uint16_t udp_src = (payload[40] << 8) | payload[41];
        uint16_t udp_dst = (payload[42] << 8) | payload[43];
        uint16_t udp_len = (payload[44] << 8) | payload[45];
        size_t sip_len = udp_len - 8;

        /* Write SIP message to out_file */
        FILE *out = fopen(out_file, "wb");
        if (!out) { perror("fopen out_file"); return 1; }
        fwrite(payload + 48, 1, sip_len, out);
        fclose(out);

        char addr_str[64];
        inet_ntop(AF_INET6, &src.sin6_addr, addr_str, sizeof(addr_str));
        fprintf(stderr, "received ESP spi=0x%08x seq=%u from %s, inner %zu bytes, wrote %zu bytes to %s\n",
                pkt_spi, seq, addr_str, inner_len, sip_len, out_file);
        close(sock);
        printf("ok\n");
        return 0;
    }

    fprintf(stderr, "timeout: no ESP packet received\n");
    close(sock);
    return 1;
}

/* ---- main ---- */

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage:\n");
        fprintf(stderr, "  esp_helper --send <sip_file> <ue> <peer> <spi_out> <auth_key_hex> <src_port> <dst_port>\n");
        fprintf(stderr, "  esp_helper --recv <ue> <peer> <spi_in> <auth_key_hex> <out_file> <timeout_sec>\n");
        fprintf(stderr, "  esp_helper --probe <ue> <peer>\n");
        return 2;
    }

    if (strcmp(argv[1], "--send") == 0) {
        if (argc < 9) {
            fprintf(stderr, "usage: esp_helper --send <sip_file> <ue> <peer> <spi_out> <auth_key_hex> <src_port> <dst_port>\n");
            return 2;
        }
        return do_send(argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8]);
    }

    if (strcmp(argv[1], "--recv") == 0) {
        if (argc < 8) {
            fprintf(stderr, "usage: esp_helper --recv <ue> <peer> <spi_in> <auth_key_hex> <out_file> <timeout_sec>\n");
            return 2;
        }
        return do_recv(argv[2], argv[3], argv[4], argv[5], argv[6], atoi(argv[7]));
    }

    if (strcmp(argv[1], "--probe") == 0) {
        if (argc < 4) {
            fprintf(stderr, "usage: esp_helper --probe <ue> <peer>\n");
            return 2;
        }
        struct in6_addr ue, peer;
        if (inet_pton(AF_INET6, argv[2], &ue) != 1 ||
            inet_pton(AF_INET6, argv[3], &peer) != 1) {
            fprintf(stderr, "bad address\n");
            return 1;
        }
        /* Send ICMPv6 echo request */
        int sock = socket(AF_INET6, SOCK_RAW, IPPROTO_ICMPV6);
        if (sock < 0) { perror("socket"); return 1; }
        struct icmp6_hdr hdr;
        memset(&hdr, 0, sizeof(hdr));
        hdr.icmp6_type = ICMP6_ECHO_REQUEST;
        hdr.icmp6_code = 0;
        hdr.icmp6_id = htons(1234);
        hdr.icmp6_seq = htons(1);
        struct sockaddr_in6 dst;
        memset(&dst, 0, sizeof(dst));
        dst.sin6_family = AF_INET6;
        dst.sin6_addr = peer;
        if (sendto(sock, &hdr, sizeof(hdr), 0, (struct sockaddr *)&dst, sizeof(dst)) < 0) {
            perror("sendto");
            close(sock);
            return 1;
        }
        printf("probe sent\n");
        close(sock);
        return 0;
    }

    fprintf(stderr, "unknown mode: %s\n", argv[1]);
    return 2;
}