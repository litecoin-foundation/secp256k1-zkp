/**********************************************************************
 * Copyright (c) 2018 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_BULLETPROOF_UTIL
#define SECP256K1_MODULE_BULLETPROOF_UTIL

/* floor(log2(n)) which returns 0 for 0, since this is used to estimate proof sizes */
SECP256K1_INLINE static size_t secp256k1_floor_lg(size_t n) {
    switch (n) {
    case 0: return 0;
    case 1: return 0;
    case 2: return 1;
    case 3: return 1;
    case 4: return 2;
    case 5: return 2;
    case 6: return 2;
    case 7: return 2;
    case 8: return 3;
    default: {
        size_t i = 0;
        while (n > 1) {
            n /= 2;
            i++;
        }
        return i;
    }
    }
}

SECP256K1_INLINE static size_t secp256k1_popcountl(unsigned long x) {
#ifdef HAVE_BUILTIN_POPCOUNTL
    return __builtin_popcountl(x);
#else
    size_t ret = 0;
    size_t i;
    for (i = 0; i < 64; i++) {
        ret += x & 1;
        x >>= 1;
    }
    return ret;
#endif
}

SECP256K1_INLINE static size_t secp256k1_ctzl(unsigned long x) {
#ifdef HAVE_BUILTIN_CTZL
    return __builtin_ctzl(x);
#else
    size_t i;
    for (i = 0; i < 64; i++) {
        if (x & (1ull << i)) {
            return i;
        }
    }
    /* If no bits are set, the result is __builtin_ctzl is undefined,
     * so we can return whatever we want here. */
    return 0;
#endif
}

static void secp256k1_scalar_dot_product(secp256k1_scalar *r, const secp256k1_scalar *a, const secp256k1_scalar *b, size_t n) {
    secp256k1_scalar_clear(r);
    while(n--) {
        secp256k1_scalar term;
        secp256k1_scalar_mul(&term, &a[n], &b[n]);
        secp256k1_scalar_add(r, r, &term);
    }
}

static void secp256k1_scalar_inverse_all_var(secp256k1_scalar *r, const secp256k1_scalar *a, size_t len) {
    secp256k1_scalar u;
    size_t i;
    if (len < 1) {
        return;
    }

    VERIFY_CHECK((r + len <= a) || (a + len <= r));

    r[0] = a[0];

    i = 0;
    while (++i < len) {
        secp256k1_scalar_mul(&r[i], &r[i - 1], &a[i]);
    }

    secp256k1_scalar_inverse_var(&u, &r[--i]);

    while (i > 0) {
        size_t j = i--;
        secp256k1_scalar_mul(&r[j], &r[i], &u);
        secp256k1_scalar_mul(&u, &u, &a[j]);
    }

    r[0] = u;
}

SECP256K1_INLINE static void secp256k1_bulletproof_serialize_points(unsigned char *out, secp256k1_ge *pt, size_t n) {
    const size_t bitveclen = (n + 7) / 8;
    size_t i;

    memset(out, 0, bitveclen);
    for (i = 0; i < n; i++) {
        secp256k1_fe pointx;
        pointx = pt[i].x;
        secp256k1_fe_normalize(&pointx);
        secp256k1_fe_get_b32(&out[bitveclen + i*32], &pointx);
        if (!secp256k1_fe_is_square_var(&pt[i].y)) {
            out[i/8] |= (1ull << (i % 8));
        }
    }
}

SECP256K1_INLINE static int secp256k1_bulletproof_deserialize_point(secp256k1_ge *pt, const unsigned char *data, size_t i, size_t n) {
    const size_t bitveclen = (n + 7) / 8;
    const size_t offset = bitveclen + i*32;
    secp256k1_fe fe;

    secp256k1_fe_set_b32_mod(&fe, &data[offset]);
    if (secp256k1_ge_set_xquad(pt, &fe)) {
        if (data[i / 8] & (1 << (i % 8))) {
            secp256k1_ge_neg(pt, pt);
        }
        return 1;
    } else {
        return 0;
    }
}

static void secp256k1_bulletproof_update_commit(unsigned char *commit, const secp256k1_ge *lpt, const secp256k1_ge *rpt) {
    secp256k1_fe pointx;
    secp256k1_sha256 sha256;
    unsigned char lrparity;
    lrparity = (!secp256k1_fe_is_square_var(&lpt->y) << 1) + !secp256k1_fe_is_square_var(&rpt->y);
    secp256k1_sha256_initialize(&sha256);
    secp256k1_sha256_write(&sha256, commit, 32);
    secp256k1_sha256_write(&sha256, &lrparity, 1);
    pointx = lpt->x;
    secp256k1_fe_normalize(&pointx);
    secp256k1_fe_get_b32(commit, &pointx);
    secp256k1_sha256_write(&sha256, commit, 32);
    pointx = rpt->x;
    secp256k1_fe_normalize(&pointx);
    secp256k1_fe_get_b32(commit, &pointx);
    secp256k1_sha256_write(&sha256, commit, 32);
    secp256k1_sha256_finalize(&sha256, commit);
}

/* ChaCha20-based deterministic scalar generation used by the Bulletproofs
 * prover. Produces two scalars per call, retrying with an incremented
 * domain-separation counter if either falls outside [1, n).
 *
 * Byte layout matches the original 4x64/8x32-limb implementation: the i-th
 * ChaCha20 output word is written in little-endian byte order into the
 * scalar's big-endian byte representation starting at byte offset 4*i, so
 * `secp256k1_scalar_set_b32` reconstructs the same scalar value the limb
 * code produced. */
static void secp256k1_scalar_chacha20(secp256k1_scalar *r1, secp256k1_scalar *r2,
                                      const unsigned char *seed, uint64_t idx) {
    uint32_t seed32[8];
    uint32_t s[16];
    uint32_t x[16];
    unsigned char buf1[32], buf2[32];
    uint32_t over_count = 0;
    int over1 = 0, over2 = 0;
    size_t i;

    for (i = 0; i < 8; i++) {
        seed32[i] = (uint32_t)seed[4 * i]
                  | ((uint32_t)seed[4 * i + 1] <<  8)
                  | ((uint32_t)seed[4 * i + 2] << 16)
                  | ((uint32_t)seed[4 * i + 3] << 24);
    }
    s[0]  = 0x61707865u; s[1]  = 0x3320646eu; s[2]  = 0x79622d32u; s[3]  = 0x6b206574u;
    s[4]  = seed32[0];   s[5]  = seed32[1];   s[6]  = seed32[2];   s[7]  = seed32[3];
    s[8]  = seed32[4];   s[9]  = seed32[5];   s[10] = seed32[6];   s[11] = seed32[7];
    s[12] = (uint32_t)idx;
    s[13] = (uint32_t)(idx >> 32);
    s[14] = 0;
    /* s[15] is the per-retry domain separator; the rest of `s` is invariant. */

    do {
        size_t r;
        s[15] = over_count;
        for (i = 0; i < 16; i++) x[i] = s[i];

#define ROTL32(v, n) (((v) << (n)) | ((v) >> (32 - (n))))
#define QR(a, b, c, d) do { \
    x[a] += x[b]; x[d] = ROTL32(x[d] ^ x[a], 16); \
    x[c] += x[d]; x[b] = ROTL32(x[b] ^ x[c], 12); \
    x[a] += x[b]; x[d] = ROTL32(x[d] ^ x[a],  8); \
    x[c] += x[d]; x[b] = ROTL32(x[b] ^ x[c],  7); \
} while (0)
        for (r = 0; r < 10; r++) {
            QR(0, 4, 8, 12); QR(1, 5, 9, 13); QR(2, 6, 10, 14); QR(3, 7, 11, 15);
            QR(0, 5, 10, 15); QR(1, 6, 11, 12); QR(2, 7, 8, 13); QR(3, 4, 9, 14);
        }
        for (i = 0; i < 16; i++) x[i] += s[i];
#undef QR
#undef ROTL32

        for (i = 0; i < 8; i++) {
            buf1[4 * i]     = (unsigned char)(x[i] & 0xff);
            buf1[4 * i + 1] = (unsigned char)((x[i] >> 8) & 0xff);
            buf1[4 * i + 2] = (unsigned char)((x[i] >> 16) & 0xff);
            buf1[4 * i + 3] = (unsigned char)((x[i] >> 24) & 0xff);
            buf2[4 * i]     = (unsigned char)(x[i + 8] & 0xff);
            buf2[4 * i + 1] = (unsigned char)((x[i + 8] >> 8) & 0xff);
            buf2[4 * i + 2] = (unsigned char)((x[i + 8] >> 16) & 0xff);
            buf2[4 * i + 3] = (unsigned char)((x[i + 8] >> 24) & 0xff);
        }
        secp256k1_scalar_set_b32(r1, buf1, &over1);
        secp256k1_scalar_set_b32(r2, buf2, &over2);
        over_count++;
    } while (over1 | over2);

    /* Wipe everything that carried keystream / keyed state. */
    memset(buf1, 0, sizeof(buf1));
    memset(buf2, 0, sizeof(buf2));
    memset(x, 0, sizeof(x));
    memset(s, 0, sizeof(s));
    memset(seed32, 0, sizeof(seed32));
}

#endif
