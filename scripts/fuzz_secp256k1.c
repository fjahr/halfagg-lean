/* Differential test driver for libsecp256k1's schnorrsig_halfagg module.
 *
 * Reads the cases of scripts/fuzz.py from standard input (see scripts/Fuzz.lean
 * for the format) and prints one result per line. Cases the C API cannot
 * express print SKIP: public keys, messages or signatures of the wrong length,
 * an input aggregate of the wrong length for IncAggregate, and public keys
 * that are not on the curve for Aggregate and IncAggregate. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <secp256k1.h>
#include <secp256k1_extrakeys.h>
#include <secp256k1_schnorrsig_halfagg.h>

#define MAXN 64

static int hexval(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

/* Decode a hex field ("_" is empty). Returns the length, or -1 if it does not fit. */
static long unhex(const char *s, size_t slen, unsigned char *out, size_t cap) {
    size_t i;
    if (slen == 1 && s[0] == '_') return 0;
    if (slen % 2 || slen / 2 > cap) return -1;
    for (i = 0; i < slen / 2; i++) out[i] = (unsigned char)(hexval(s[2 * i]) * 16 + hexval(s[2 * i + 1]));
    return (long)(slen / 2);
}

/* Parse "a:b[:c],..." (or "-") into fixed-size fields. Returns the item count,
 * -1 if a field has the wrong length, -2 if a public key is not on the curve. */
static int parse_items(const secp256k1_context *ctx, char *s, int with_sig,
                       secp256k1_xonly_pubkey *pks, unsigned char *msgs, unsigned char *sigs) {
    int n = 0, bad_len = 0, bad_pk = 0;
    char *item, *save1;
    if (strcmp(s, "-") == 0) return 0;
    for (item = strtok_r(s, ",", &save1); item != NULL; item = strtok_r(NULL, ",", &save1)) {
        unsigned char pk[32];
        char *f[3] = {NULL, NULL, NULL};
        char *p = item;
        int k = 0;
        if (n >= MAXN) return -1;
        f[k++] = p;
        while ((p = strchr(p, ':')) != NULL && k < 3) { *p++ = 0; f[k++] = p; }
        if (k != (with_sig ? 3 : 2)) return -1;
        if (unhex(f[0], strlen(f[0]), pk, 32) != 32) bad_len = 1;
        else if (!secp256k1_xonly_pubkey_parse(ctx, &pks[n], pk)) bad_pk = 1;
        if (unhex(f[1], strlen(f[1]), msgs + 32 * n, 32) != 32) bad_len = 1;
        if (with_sig && unhex(f[2], strlen(f[2]), sigs + 64 * n, 64) != 64) bad_len = 1;
        n++;
    }
    return bad_len ? -1 : bad_pk ? -2 : n;
}

static void print_hex(const unsigned char *b, size_t len) {
    size_t i;
    for (i = 0; i < len; i++) printf("%02x", b[i]);
    printf("\n");
}

int main(void) {
    secp256k1_context *ctx = secp256k1_context_create(SECP256K1_CONTEXT_NONE);
    static char line[1 << 16];
    static secp256k1_xonly_pubkey pks[2 * MAXN];
    static unsigned char msgs[32 * 2 * MAXN], sigs[64 * MAXN], agg[32 * (2 * MAXN + 2)];

    while (fgets(line, sizeof(line), stdin) != NULL) {
        char *save, *kind, *a, *b, *c;
        line[strcspn(line, "\n")] = 0;
        kind = strtok_r(line, " ", &save);
        a = strtok_r(NULL, " ", &save);
        b = strtok_r(NULL, " ", &save);
        c = strtok_r(NULL, " ", &save);
        if (kind == NULL || a == NULL) { printf("BADLINE\n"); continue; }
        if (kind[0] == 'A') {
            int n = parse_items(ctx, a, 1, pks, msgs, sigs);
            size_t len = sizeof(agg);
            if (n < 0) { printf("SKIP\n"); continue; }
            if (secp256k1_schnorrsig_aggregate(ctx, agg, &len, pks, msgs, sigs, (size_t)n)) print_hex(agg, len);
            else printf("FAIL\n");
        } else if (kind[0] == 'I' && b != NULL && c != NULL) {
            long alen = unhex(a, strlen(a), agg, sizeof(agg) / 2);
            int v = parse_items(ctx, b, 0, pks, msgs, NULL);
            int u = v < 0 ? v : parse_items(ctx, c, 1, pks + v, msgs + 32 * v, sigs);
            size_t len = sizeof(agg);
            if (v < 0 || u < 0 || alen != 32 * ((long)v + 1)) { printf("SKIP\n"); continue; }
            if (secp256k1_schnorrsig_inc_aggregate(ctx, agg, &len, pks, msgs, sigs, (size_t)v, (size_t)u)) print_hex(agg, len);
            else printf("FAIL\n");
        } else if (kind[0] == 'V' && b != NULL) {
            long alen = unhex(a, strlen(a), agg, sizeof(agg));
            int n = parse_items(ctx, b, 0, pks, msgs, NULL);
            if (n == -1 || alen < 0) { printf("SKIP\n"); continue; }
            /* a public key that fails lift_x makes VerifyAggregate return false */
            if (n == -2) { printf("false\n"); continue; }
            printf(secp256k1_schnorrsig_aggverify(ctx, pks, msgs, (size_t)n, agg, (size_t)alen) ? "true\n" : "false\n");
        } else {
            printf("BADLINE\n");
        }
    }
    secp256k1_context_destroy(ctx);
    return 0;
}
