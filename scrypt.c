/*-
 * Copyright 2009 Colin Percival, 2011 ArtForz
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file was originally written by Colin Percival as part of the Tarsnap
 * online backup system.
 */

#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <x86intrin.h>

#include "cpuminer-config.h"
#include "miner.h"

#define byteswap(x) ((((x) << 24) & 0xff000000u) | (((x) << 8) & 0x00ff0000u) | (((x) >> 8) & 0x0000ff00u) | (((x) >> 24) & 0x000000ffu))

typedef struct SHA256Context {
	uint32_t state[8];
	uint32_t buf[16];
} SHA256_CTX;

/*
 * Encode a length len/4 vector of (uint32_t) into a length len vector of
 * (unsigned char) in big-endian form.  Assumes len is a multiple of 4.
 */
static inline void
be32enc_vect(uint32_t *dst, const uint32_t *src, uint32_t len)
{
	uint32_t i;

	for (i = 0; i < len; i++)
		dst[i] = byteswap(src[i]);
}

/* Elementary functions used by SHA256 */
#define Ch(x, y, z)	((x & (y ^ z)) ^ z)
#define Maj(x, y, z)	((x & (y | z)) | (y & z))
#define SHR(x, n)	(x >> n)
#define ROTR(x, n)	((x >> n) | (x << (32 - n)))
#define S0(x)		(ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define S1(x)		(ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define s0(x)		(ROTR(x, 7) ^ ROTR(x, 18) ^ SHR(x, 3))
#define s1(x)		(ROTR(x, 17) ^ ROTR(x, 19) ^ SHR(x, 10))

/* SHA256 round function */
#define RND(a, b, c, d, e, f, g, h, k)			\
	t0 = h + S1(e) + Ch(e, f, g) + k;		\
	t1 = S0(a) + Maj(a, b, c);			\
	d += t0;					\
	h  = t0 + t1;

/* Adjusted round function for rotating state */
#define RNDr(S, W, i, k)			\
	RND(S[(64 - i) % 8], S[(65 - i) % 8],	\
	    S[(66 - i) % 8], S[(67 - i) % 8],	\
	    S[(68 - i) % 8], S[(69 - i) % 8],	\
	    S[(70 - i) % 8], S[(71 - i) % 8],	\
	    W[i] + k)

/*
 * SHA256 block compression function.  The 256-bit state is transformed via
 * the 512-bit input block to produce a new state.
 */
static void
SHA256_Transform(uint32_t * state, const uint32_t block[16], int swap)
{
	uint32_t W[64];
	uint32_t S[8];
	uint32_t t0, t1;
	int i;

	/* 1. Prepare message schedule W. */
	if(swap)
		for (i = 0; i < 16; i++)
			W[i] = byteswap(block[i]);
	else
		memcpy(W, block, 64);
	for (i = 16; i < 64; i += 2) {
		W[i] = s1(W[i - 2]) + W[i - 7] + s0(W[i - 15]) + W[i - 16];
		W[i+1] = s1(W[i - 1]) + W[i - 6] + s0(W[i - 14]) + W[i - 15];
	}

	/* 2. Initialize working variables. */
	memcpy(S, state, 32);

	/* 3. Mix. */
	RNDr(S, W, 0, 0x428a2f98);
	RNDr(S, W, 1, 0x71374491);
	RNDr(S, W, 2, 0xb5c0fbcf);
	RNDr(S, W, 3, 0xe9b5dba5);
	RNDr(S, W, 4, 0x3956c25b);
	RNDr(S, W, 5, 0x59f111f1);
	RNDr(S, W, 6, 0x923f82a4);
	RNDr(S, W, 7, 0xab1c5ed5);
	RNDr(S, W, 8, 0xd807aa98);
	RNDr(S, W, 9, 0x12835b01);
	RNDr(S, W, 10, 0x243185be);
	RNDr(S, W, 11, 0x550c7dc3);
	RNDr(S, W, 12, 0x72be5d74);
	RNDr(S, W, 13, 0x80deb1fe);
	RNDr(S, W, 14, 0x9bdc06a7);
	RNDr(S, W, 15, 0xc19bf174);
	RNDr(S, W, 16, 0xe49b69c1);
	RNDr(S, W, 17, 0xefbe4786);
	RNDr(S, W, 18, 0x0fc19dc6);
	RNDr(S, W, 19, 0x240ca1cc);
	RNDr(S, W, 20, 0x2de92c6f);
	RNDr(S, W, 21, 0x4a7484aa);
	RNDr(S, W, 22, 0x5cb0a9dc);
	RNDr(S, W, 23, 0x76f988da);
	RNDr(S, W, 24, 0x983e5152);
	RNDr(S, W, 25, 0xa831c66d);
	RNDr(S, W, 26, 0xb00327c8);
	RNDr(S, W, 27, 0xbf597fc7);
	RNDr(S, W, 28, 0xc6e00bf3);
	RNDr(S, W, 29, 0xd5a79147);
	RNDr(S, W, 30, 0x06ca6351);
	RNDr(S, W, 31, 0x14292967);
	RNDr(S, W, 32, 0x27b70a85);
	RNDr(S, W, 33, 0x2e1b2138);
	RNDr(S, W, 34, 0x4d2c6dfc);
	RNDr(S, W, 35, 0x53380d13);
	RNDr(S, W, 36, 0x650a7354);
	RNDr(S, W, 37, 0x766a0abb);
	RNDr(S, W, 38, 0x81c2c92e);
	RNDr(S, W, 39, 0x92722c85);
	RNDr(S, W, 40, 0xa2bfe8a1);
	RNDr(S, W, 41, 0xa81a664b);
	RNDr(S, W, 42, 0xc24b8b70);
	RNDr(S, W, 43, 0xc76c51a3);
	RNDr(S, W, 44, 0xd192e819);
	RNDr(S, W, 45, 0xd6990624);
	RNDr(S, W, 46, 0xf40e3585);
	RNDr(S, W, 47, 0x106aa070);
	RNDr(S, W, 48, 0x19a4c116);
	RNDr(S, W, 49, 0x1e376c08);
	RNDr(S, W, 50, 0x2748774c);
	RNDr(S, W, 51, 0x34b0bcb5);
	RNDr(S, W, 52, 0x391c0cb3);
	RNDr(S, W, 53, 0x4ed8aa4a);
	RNDr(S, W, 54, 0x5b9cca4f);
	RNDr(S, W, 55, 0x682e6ff3);
	RNDr(S, W, 56, 0x748f82ee);
	RNDr(S, W, 57, 0x78a5636f);
	RNDr(S, W, 58, 0x84c87814);
	RNDr(S, W, 59, 0x8cc70208);
	RNDr(S, W, 60, 0x90befffa);
	RNDr(S, W, 61, 0xa4506ceb);
	RNDr(S, W, 62, 0xbef9a3f7);
	RNDr(S, W, 63, 0xc67178f2);

	/* 4. Mix local working variables into global state */
	for (i = 0; i < 8; i++)
		state[i] += S[i];
}

static inline void
SHA256_InitState(uint32_t * state)
{
	/* Magic initialization constants */
	state[0] = 0x6A09E667;
	state[1] = 0xBB67AE85;
	state[2] = 0x3C6EF372;
	state[3] = 0xA54FF53A;
	state[4] = 0x510E527F;
	state[5] = 0x9B05688C;
	state[6] = 0x1F83D9AB;
	state[7] = 0x5BE0CD19;
}

static const uint32_t passwdpad[12] = {0x00000080, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80020000};
static const uint32_t outerpad[8] = {0x80000000, 0, 0, 0, 0, 0, 0, 0x00000300};

/**
 * PBKDF2_SHA256(passwd, passwdlen, salt, saltlen, c, buf, dkLen):
 * Compute PBKDF2(passwd, salt, c, dkLen) using HMAC-SHA256 as the PRF, and
 * write the output to buf.  The value dkLen must be at most 32 * (2^32 - 1).
 */
static inline void
PBKDF2_SHA256_80_128(const uint32_t * passwd, uint32_t * buf)
{
	SHA256_CTX PShictx, PShoctx;
	uint32_t tstate[8];
	uint32_t ihash[8];
	uint32_t i;
	uint32_t pad[16];
	
	static const uint32_t innerpad[11] = {0x00000080, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xa0040000};

	/* If Klen > 64, the key is really SHA256(K). */
	SHA256_InitState(tstate);
	SHA256_Transform(tstate, passwd, 1);
	memcpy(pad, passwd+16, 16);
	memcpy(pad+4, passwdpad, 48);
	SHA256_Transform(tstate, pad, 1);
	memcpy(ihash, tstate, 32);

	SHA256_InitState(PShictx.state);
	for (i = 0; i < 8; i++)
		pad[i] = ihash[i] ^ 0x36363636;
	for (; i < 16; i++)
		pad[i] = 0x36363636;
	SHA256_Transform(PShictx.state, pad, 0);
	SHA256_Transform(PShictx.state, passwd, 1);
	be32enc_vect(PShictx.buf, passwd+16, 4);
	be32enc_vect(PShictx.buf+5, innerpad, 11);

	SHA256_InitState(PShoctx.state);
	for (i = 0; i < 8; i++)
		pad[i] = ihash[i] ^ 0x5c5c5c5c;
	for (; i < 16; i++)
		pad[i] = 0x5c5c5c5c;
	SHA256_Transform(PShoctx.state, pad, 0);
	memcpy(PShoctx.buf+8, outerpad, 32);

	/* Iterate through the blocks. */
	for (i = 0; i < 4; i++) {
		uint32_t istate[8];
		uint32_t ostate[8];
		
		memcpy(istate, PShictx.state, 32);
		PShictx.buf[4] = i + 1;
		SHA256_Transform(istate, PShictx.buf, 0);
		memcpy(PShoctx.buf, istate, 32);

		memcpy(ostate, PShoctx.state, 32);
		SHA256_Transform(ostate, PShoctx.buf, 0);
		be32enc_vect(buf+i*8, ostate, 8);
	}
}


static inline uint32_t
PBKDF2_SHA256_80_128_32(const uint32_t * passwd, const uint32_t * salt)
{
	uint32_t tstate[8];
	uint32_t ostate[8];
	uint32_t ihash[8];
	uint32_t i;

	/* Compute HMAC state after processing P and S. */
	uint32_t pad[16];
	
	
	static const uint32_t ihash_finalblk[16] = {0x00000001,0x80000000,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0x00000620};

	/* If Klen > 64, the key is really SHA256(K). */
	SHA256_InitState(tstate);
	SHA256_Transform(tstate, passwd, 1);
	memcpy(pad, passwd+16, 16);
	memcpy(pad+4, passwdpad, 48);
	SHA256_Transform(tstate, pad, 1);
	memcpy(ihash, tstate, 32);

	SHA256_InitState(ostate);
	for (i = 0; i < 8; i++)
		pad[i] = ihash[i] ^ 0x5c5c5c5c;
	for (; i < 16; i++)
		pad[i] = 0x5c5c5c5c;
	SHA256_Transform(ostate, pad, 0);

	SHA256_InitState(tstate);
	for (i = 0; i < 8; i++)
		pad[i] = ihash[i] ^ 0x36363636;
	for (; i < 16; i++)
		pad[i] = 0x36363636;
	SHA256_Transform(tstate, pad, 0);
	SHA256_Transform(tstate, salt, 1);
	SHA256_Transform(tstate, salt+16, 1);
	SHA256_Transform(tstate, ihash_finalblk, 0);
	memcpy(pad, tstate, 32);
	memcpy(pad+8, outerpad, 32);

	/* Feed the inner hash to the outer SHA256 operation. */
	SHA256_Transform(ostate, pad, 0);
	/* Finish the outer SHA256 operation. */
	return byteswap(ostate[7]);
}

void
__attribute__ ((always_inline))
salsa20_8_sse2(__m128i *B, const __m128i *Bx)
{
	__m128i x00,x01,x02,x03,x04,x05,x06,x07,x08,x09,x10,x11,x12,x13,x14,x15;
	size_t i;
	__m128i tmp00;
	__m128i tmp10;
	__m128i tmp01;
	__m128i tmp11;
	__m128i tmp02;
	__m128i tmp12;
	__m128i tmp03;
	__m128i tmp13;

	x00 = (B[ 0] = _mm_xor_si128(B[ 0],Bx[ 0]));	x01 = (B[ 1] = _mm_xor_si128(B[ 1],Bx[ 1]));
	x02 = (B[ 2] = _mm_xor_si128(B[ 2],Bx[ 2]));	x03 = (B[ 3] = _mm_xor_si128(B[ 3],Bx[ 3]));
	x04 = (B[ 4] = _mm_xor_si128(B[ 4],Bx[ 4]));	x05 = (B[ 5] = _mm_xor_si128(B[ 5],Bx[ 5]));
	x06 = (B[ 6] = _mm_xor_si128(B[ 6],Bx[ 6]));	x07 = (B[ 7] = _mm_xor_si128(B[ 7],Bx[ 7]));
	x08 = (B[ 8] = _mm_xor_si128(B[ 8],Bx[ 8]));	x09 = (B[ 9] = _mm_xor_si128(B[ 9],Bx[ 9]));
	x10 = (B[10] = _mm_xor_si128(B[10],Bx[10]));	x11 = (B[11] = _mm_xor_si128(B[11],Bx[11]));
	x12 = (B[12] = _mm_xor_si128(B[12],Bx[12]));	x13 = (B[13] = _mm_xor_si128(B[13],Bx[13]));
	x14 = (B[14] = _mm_xor_si128(B[14],Bx[14]));	x15 = (B[15] = _mm_xor_si128(B[15],Bx[15]));

//	for (i = 0; i < 8; i += 2)
	{
#define R(a,n) _mm_or_si128(_mm_slli_epi32(a, n), _mm_srli_epi32(a, (32-n)))
		/* Operate on columns. */
		x04 = _mm_xor_si128(x04,R(_mm_add_epi32(x00,x12), 7));	x09 = _mm_xor_si128(x09,R(_mm_add_epi32(x05,x01), 7));
		x08 = _mm_xor_si128(x08,R(_mm_add_epi32(x04,x00), 9));	x13 = _mm_xor_si128(x13,R(_mm_add_epi32(x09,x05), 9));
		x12 = _mm_xor_si128(x12,R(_mm_add_epi32(x08,x04),13));	x01 = _mm_xor_si128(x01,R(_mm_add_epi32(x13,x09),13));
		x00 = _mm_xor_si128(x00,R(_mm_add_epi32(x12,x08),18));	x05 = _mm_xor_si128(x05,R(_mm_add_epi32(x01,x13),18));

		x14 = _mm_xor_si128(x14,R(_mm_add_epi32(x10,x06), 7));	x03 = _mm_xor_si128(x03,R(_mm_add_epi32(x15,x11), 7));
		x02 = _mm_xor_si128(x02,R(_mm_add_epi32(x14,x10), 9));	x07 = _mm_xor_si128(x07,R(_mm_add_epi32(x03,x15), 9));
		x06 = _mm_xor_si128(x06,R(_mm_add_epi32(x02,x14),13));	x11 = _mm_xor_si128(x11,R(_mm_add_epi32(x07,x03),13));
		x10 = _mm_xor_si128(x10,R(_mm_add_epi32(x06,x02),18));	x15 = _mm_xor_si128(x15,R(_mm_add_epi32(x11,x07),18));

		/* Operate on rows. */
		x01 = _mm_xor_si128(x01,R(_mm_add_epi32(x00,x03), 7));	x06 = _mm_xor_si128(x06,R(_mm_add_epi32(x05,x04), 7));
		x02 = _mm_xor_si128(x02,R(_mm_add_epi32(x01,x00), 9));	x07 = _mm_xor_si128(x07,R(_mm_add_epi32(x06,x05), 9));
		x03 = _mm_xor_si128(x03,R(_mm_add_epi32(x02,x01),13));	x04 = _mm_xor_si128(x04,R(_mm_add_epi32(x07,x06),13));
		x00 = _mm_xor_si128(x00,R(_mm_add_epi32(x03,x02),18));	x05 = _mm_xor_si128(x05,R(_mm_add_epi32(x04,x07),18));

		x11 = _mm_xor_si128(x11,R(_mm_add_epi32(x10,x09), 7));	x12 = _mm_xor_si128(x12,R(_mm_add_epi32(x15,x14), 7));
		x08 = _mm_xor_si128(x08,R(_mm_add_epi32(x11,x10), 9));	x13 = _mm_xor_si128(x13,R(_mm_add_epi32(x12,x15), 9));
		x09 = _mm_xor_si128(x09,R(_mm_add_epi32(x08,x11),13));	x14 = _mm_xor_si128(x14,R(_mm_add_epi32(x13,x12),13));
		x10 = _mm_xor_si128(x10,R(_mm_add_epi32(x09,x08),18));	x15 = _mm_xor_si128(x15,R(_mm_add_epi32(x14,x13),18));

		/* Operate on columns. */
		x04 = _mm_xor_si128(x04,R(_mm_add_epi32(x00,x12), 7));	x09 = _mm_xor_si128(x09,R(_mm_add_epi32(x05,x01), 7));
		x08 = _mm_xor_si128(x08,R(_mm_add_epi32(x04,x00), 9));	x13 = _mm_xor_si128(x13,R(_mm_add_epi32(x09,x05), 9));
		x12 = _mm_xor_si128(x12,R(_mm_add_epi32(x08,x04),13));	x01 = _mm_xor_si128(x01,R(_mm_add_epi32(x13,x09),13));
		x00 = _mm_xor_si128(x00,R(_mm_add_epi32(x12,x08),18));	x05 = _mm_xor_si128(x05,R(_mm_add_epi32(x01,x13),18));

		x14 = _mm_xor_si128(x14,R(_mm_add_epi32(x10,x06), 7));	x03 = _mm_xor_si128(x03,R(_mm_add_epi32(x15,x11), 7));
		x02 = _mm_xor_si128(x02,R(_mm_add_epi32(x14,x10), 9));	x07 = _mm_xor_si128(x07,R(_mm_add_epi32(x03,x15), 9));
		x06 = _mm_xor_si128(x06,R(_mm_add_epi32(x02,x14),13));	x11 = _mm_xor_si128(x11,R(_mm_add_epi32(x07,x03),13));
		x10 = _mm_xor_si128(x10,R(_mm_add_epi32(x06,x02),18));	x15 = _mm_xor_si128(x15,R(_mm_add_epi32(x11,x07),18));

		/* Operate on rows. */
		x01 = _mm_xor_si128(x01,R(_mm_add_epi32(x00,x03), 7));	x06 = _mm_xor_si128(x06,R(_mm_add_epi32(x05,x04), 7));
		x02 = _mm_xor_si128(x02,R(_mm_add_epi32(x01,x00), 9));	x07 = _mm_xor_si128(x07,R(_mm_add_epi32(x06,x05), 9));
		x03 = _mm_xor_si128(x03,R(_mm_add_epi32(x02,x01),13));	x04 = _mm_xor_si128(x04,R(_mm_add_epi32(x07,x06),13));
		x00 = _mm_xor_si128(x00,R(_mm_add_epi32(x03,x02),18));	x05 = _mm_xor_si128(x05,R(_mm_add_epi32(x04,x07),18));

		x11 = _mm_xor_si128(x11,R(_mm_add_epi32(x10,x09), 7));	x12 = _mm_xor_si128(x12,R(_mm_add_epi32(x15,x14), 7));
		x08 = _mm_xor_si128(x08,R(_mm_add_epi32(x11,x10), 9));	x13 = _mm_xor_si128(x13,R(_mm_add_epi32(x12,x15), 9));
		x09 = _mm_xor_si128(x09,R(_mm_add_epi32(x08,x11),13));	x14 = _mm_xor_si128(x14,R(_mm_add_epi32(x13,x12),13));
		x10 = _mm_xor_si128(x10,R(_mm_add_epi32(x09,x08),18));	x15 = _mm_xor_si128(x15,R(_mm_add_epi32(x14,x13),18));

		/* Operate on columns. */
		x04 = _mm_xor_si128(x04,R(_mm_add_epi32(x00,x12), 7));	x09 = _mm_xor_si128(x09,R(_mm_add_epi32(x05,x01), 7));
		x08 = _mm_xor_si128(x08,R(_mm_add_epi32(x04,x00), 9));	x13 = _mm_xor_si128(x13,R(_mm_add_epi32(x09,x05), 9));
		x12 = _mm_xor_si128(x12,R(_mm_add_epi32(x08,x04),13));	x01 = _mm_xor_si128(x01,R(_mm_add_epi32(x13,x09),13));
		x00 = _mm_xor_si128(x00,R(_mm_add_epi32(x12,x08),18));	x05 = _mm_xor_si128(x05,R(_mm_add_epi32(x01,x13),18));

		x14 = _mm_xor_si128(x14,R(_mm_add_epi32(x10,x06), 7));	x03 = _mm_xor_si128(x03,R(_mm_add_epi32(x15,x11), 7));
		x02 = _mm_xor_si128(x02,R(_mm_add_epi32(x14,x10), 9));	x07 = _mm_xor_si128(x07,R(_mm_add_epi32(x03,x15), 9));
		x06 = _mm_xor_si128(x06,R(_mm_add_epi32(x02,x14),13));	x11 = _mm_xor_si128(x11,R(_mm_add_epi32(x07,x03),13));
		x10 = _mm_xor_si128(x10,R(_mm_add_epi32(x06,x02),18));	x15 = _mm_xor_si128(x15,R(_mm_add_epi32(x11,x07),18));

		/* Operate on rows. */
		x01 = _mm_xor_si128(x01,R(_mm_add_epi32(x00,x03), 7));	x06 = _mm_xor_si128(x06,R(_mm_add_epi32(x05,x04), 7));
		x02 = _mm_xor_si128(x02,R(_mm_add_epi32(x01,x00), 9));	x07 = _mm_xor_si128(x07,R(_mm_add_epi32(x06,x05), 9));
		x03 = _mm_xor_si128(x03,R(_mm_add_epi32(x02,x01),13));	x04 = _mm_xor_si128(x04,R(_mm_add_epi32(x07,x06),13));
		x00 = _mm_xor_si128(x00,R(_mm_add_epi32(x03,x02),18));	x05 = _mm_xor_si128(x05,R(_mm_add_epi32(x04,x07),18));

		x11 = _mm_xor_si128(x11,R(_mm_add_epi32(x10,x09), 7));	x12 = _mm_xor_si128(x12,R(_mm_add_epi32(x15,x14), 7));
		x08 = _mm_xor_si128(x08,R(_mm_add_epi32(x11,x10), 9));	x13 = _mm_xor_si128(x13,R(_mm_add_epi32(x12,x15), 9));
		x09 = _mm_xor_si128(x09,R(_mm_add_epi32(x08,x11),13));	x14 = _mm_xor_si128(x14,R(_mm_add_epi32(x13,x12),13));
		x10 = _mm_xor_si128(x10,R(_mm_add_epi32(x09,x08),18));	x15 = _mm_xor_si128(x15,R(_mm_add_epi32(x14,x13),18));


		/* Operate on columns. */
		x04 = _mm_xor_si128(x04,R(_mm_add_epi32(x00,x12), 7));	x09 = _mm_xor_si128(x09,R(_mm_add_epi32(x05,x01), 7));
		x08 = _mm_xor_si128(x08,R(_mm_add_epi32(x04,x00), 9));	x13 = _mm_xor_si128(x13,R(_mm_add_epi32(x09,x05), 9));
		x12 = _mm_xor_si128(x12,R(_mm_add_epi32(x08,x04),13));	x01 = _mm_xor_si128(x01,R(_mm_add_epi32(x13,x09),13));
		x00 = _mm_xor_si128(x00,R(_mm_add_epi32(x12,x08),18));	x05 = _mm_xor_si128(x05,R(_mm_add_epi32(x01,x13),18));

		x14 = _mm_xor_si128(x14,R(_mm_add_epi32(x10,x06), 7));	x03 = _mm_xor_si128(x03,R(_mm_add_epi32(x15,x11), 7));
		x02 = _mm_xor_si128(x02,R(_mm_add_epi32(x14,x10), 9));	x07 = _mm_xor_si128(x07,R(_mm_add_epi32(x03,x15), 9));
		x06 = _mm_xor_si128(x06,R(_mm_add_epi32(x02,x14),13));	x11 = _mm_xor_si128(x11,R(_mm_add_epi32(x07,x03),13));
		x10 = _mm_xor_si128(x10,R(_mm_add_epi32(x06,x02),18));	x15 = _mm_xor_si128(x15,R(_mm_add_epi32(x11,x07),18));

		/* Operate on rows. */
		x01 = _mm_xor_si128(x01,R(_mm_add_epi32(x00,x03), 7));	x06 = _mm_xor_si128(x06,R(_mm_add_epi32(x05,x04), 7));
		x02 = _mm_xor_si128(x02,R(_mm_add_epi32(x01,x00), 9));	x07 = _mm_xor_si128(x07,R(_mm_add_epi32(x06,x05), 9));
		x03 = _mm_xor_si128(x03,R(_mm_add_epi32(x02,x01),13));	x04 = _mm_xor_si128(x04,R(_mm_add_epi32(x07,x06),13));
		x00 = _mm_xor_si128(x00,R(_mm_add_epi32(x03,x02),18));	x05 = _mm_xor_si128(x05,R(_mm_add_epi32(x04,x07),18));

		x11 = _mm_xor_si128(x11,R(_mm_add_epi32(x10,x09), 7));	x12 = _mm_xor_si128(x12,R(_mm_add_epi32(x15,x14), 7));
		x08 = _mm_xor_si128(x08,R(_mm_add_epi32(x11,x10), 9));	x13 = _mm_xor_si128(x13,R(_mm_add_epi32(x12,x15), 9));
		x09 = _mm_xor_si128(x09,R(_mm_add_epi32(x08,x11),13));	x14 = _mm_xor_si128(x14,R(_mm_add_epi32(x13,x12),13));
		x10 = _mm_xor_si128(x10,R(_mm_add_epi32(x09,x08),18));	x15 = _mm_xor_si128(x15,R(_mm_add_epi32(x14,x13),18));
#undef R
	}

	B[ 0]=_mm_add_epi32(B[ 0] , x00);	B[ 1]=_mm_add_epi32(B[ 1] , x01);
	B[ 2]=_mm_add_epi32(B[ 2] , x02);	B[ 3]=_mm_add_epi32(B[ 3] , x03);
	B[ 4]=_mm_add_epi32(B[ 4] , x04);	B[ 5]=_mm_add_epi32(B[ 5] , x05);
	B[ 6]=_mm_add_epi32(B[ 6] , x06);	B[ 7]=_mm_add_epi32(B[ 7] , x07);
	B[ 8]=_mm_add_epi32(B[ 8] , x08);	B[ 9]=_mm_add_epi32(B[ 9] , x09);
	B[10]=_mm_add_epi32(B[10] , x10);	B[11]=_mm_add_epi32(B[11] , x11);
	B[12]=_mm_add_epi32(B[12] , x12);	B[13]=_mm_add_epi32(B[13] , x13);
	B[14]=_mm_add_epi32(B[14] , x14);	B[15]=_mm_add_epi32(B[15] , x15);

}


static uint32_t scrypt_1024_1_1_256_sp(const uint32_t* input, unsigned char* scratchpad, unsigned int *V1)
{
	uint32_t * V;
	uint32_t X[256];
	uint32_t X1[256];
	uint32_t i;
	uint32_t j;
	uint32_t k;
	uint32_t *p1, *p2;

	uint32_t Htarg = V1[0];
	uint32_t ret;

	p1 = (uint32_t *)X;
	V = (uint32_t *)(scratchpad);

	PBKDF2_SHA256_80_128(input, X1);
	PBKDF2_SHA256_80_128(&input[32], &X1[32]);
	PBKDF2_SHA256_80_128(&input[64], &X1[64]);
	PBKDF2_SHA256_80_128(&input[96], &X1[96]);
	
	for(i=0;i<16;i++){
		X[4*i+0] = X1[i+00];
		X[4*i+1] = X1[i+32];
		X[4*i+2] = X1[i+64];
		X[4*i+3] = X1[i+96];

		X[4*i+0 + 64] = X1[i+00+16];
		X[4*i+1 + 64] = X1[i+32+16];
		X[4*i+2 + 64] = X1[i+64+16];
		X[4*i+3 + 64] = X1[i+96+16];
	}


	for (i = 0; i < 1024; i += 1){
		memcpy(&V[4*i * 32], X, 4*128);

		salsa20_8_sse2((__m128i *)&X[0], (__m128i *)&X[64]);
		salsa20_8_sse2((__m128i *)&X[64], (__m128i *)&X[0]);

//		memcpy(&V[4*(i + 1) * 32], X, 4*128);
//		salsa20_8_sse2((__m128i *)&X[0], (__m128i *)&X[64]);
//		salsa20_8_sse2((__m128i *)&X[64], (__m128i *)&X[0]);
	}


	for (i = 0; i < 1024; i += 1) {

		j = X[64] & 1023;
		p2 = (uint32_t *)(&V[4*j * 32]);
		for(k = 0; k < 32; k++)
			p1[4*k] ^= p2[4*k];

		j = X[64+1] & 1023;
		p2 = (uint32_t *)(&V[4*j * 32]);
		for(k = 0; k < 32; k++)
			p1[4*k+1] ^= p2[4*k+1];

		j = X[64+2] & 1023;
		p2 = (uint32_t *)(&V[4*j * 32]);
		for(k = 0; k < 32; k++)
			p1[4*k+2] ^= p2[4*k+2];

		j = X[64+3] & 1023;
		p2 = (uint32_t *)(&V[4*j * 32]);
		for(k = 0; k < 32; k++)
			p1[4*k+3] ^= p2[4*k+3];

		salsa20_8_sse2((__m128i *)&X[0], (__m128i *)&X[64]);
		salsa20_8_sse2((__m128i *)&X[64], (__m128i *)&X[0]);
/*
		j = X[64] & 1023;
		p2 = (uint32_t *)(&V[4*j * 32]);
		for(k = 0; k < 32; k++)
			p1[4*k] ^= p2[4*k];

		j = X[64+1] & 1023;
		p2 = (uint32_t *)(&V[4*j * 32]);
		for(k = 0; k < 32; k++)
			p1[4*k+1] ^= p2[4*k+1];

		j = X[64+2] & 1023;
		p2 = (uint32_t *)(&V[4*j * 32]);
		for(k = 0; k < 32; k++)
			p1[4*k+2] ^= p2[4*k+2];

		j = X[64+3] & 1023;
		p2 = (uint32_t *)(&V[4*j * 32]);
		for(k = 0; k < 32; k++)
			p1[4*k+3] ^= p2[4*k+3];

		salsa20_8_sse2((__m128i *)&X[0], (__m128i *)&X[64]);
		salsa20_8_sse2((__m128i *)&X[64], (__m128i *)&X[0]);
*/
	}

	for(i=0;i<16;i++){
		X1[i+00]=X[4*i+0];
		X1[i+32]=X[4*i+1];
		X1[i+64]=X[4*i+2];
		X1[i+96]=X[4*i+3];

		X1[i+00+16]=X[4*i+0 + 64];
		X1[i+32+16]=X[4*i+1 + 64];
		X1[i+64+16]=X[4*i+2 + 64];
		X1[i+96+16]=X[4*i+3 + 64];
	}

	V = (uint32_t *)(scratchpad);
	
	ret=PBKDF2_SHA256_80_128_32(input,	  &X1[00]);
	V1[0]	=	ret;
	if(ret<=Htarg)	return 1;
	
	ret=PBKDF2_SHA256_80_128_32(&input[32], &X1[32]);
	V1[1]	=	ret;
	if(ret<=Htarg)	return 2;
	
	ret=PBKDF2_SHA256_80_128_32(&input[64], &X1[64]);
	V1[2]	=	ret;
	if(ret<=Htarg)	return 3;
	
	ret=PBKDF2_SHA256_80_128_32(&input[96], &X1[96]);
	V1[3]	=	ret;
	if(ret<=Htarg)	return 4;
	
	return 0;
}

int scanhash_scrypt(int thr_id, unsigned char *pdata, unsigned char *scratchbuf,
	const unsigned char *ptarget,
	uint32_t max_nonce, uint32_t *hashes_done)
{
	uint32_t data[128];
	uint32_t tmp_hash7;
	uint32_t n = 0;
	uint32_t Htarg = ((const uint32_t *)ptarget)[7];
//	int i;
	unsigned int *V = (unsigned int *)(scratchbuf);
	
	unsigned int V1[16];
	
	/* TODO Htarg not correct compare */
	/* this variant it kastil' */
//	Htarg++;

	be32enc_vect(data, (const uint32_t *)pdata, 20);
	be32enc_vect(&data[32], (const uint32_t *)pdata, 20);
	be32enc_vect(&data[64], (const uint32_t *)pdata, 20);
	be32enc_vect(&data[96], (const uint32_t *)pdata, 20);
	
		n++;
	while(1) {
		data[00+19] = n+0;
		data[32+19] = n+1;
		data[64+19] = n+2;
		data[96+19] = n+3;

		V1[0]	=	Htarg;
		
		tmp_hash7 = scrypt_1024_1_1_256_sp(data, scratchbuf, V1);
		
		if (tmp_hash7 == 1) {
			((uint32_t *)pdata)[19] = byteswap(n);
			*hashes_done = n;
			return true;
		}
		if (tmp_hash7 == 2) {
			n+=1;
			((uint32_t *)pdata)[19] = byteswap(n);
			*hashes_done = n;
			return true;
		}
		if (tmp_hash7 == 3) {
			n+=2;
			((uint32_t *)pdata)[19] = byteswap(n);
			*hashes_done = n;
			return true;
		}
		if (tmp_hash7 == 4) {
			n+=3;
			((uint32_t *)pdata)[19] = byteswap(n);
			*hashes_done = n;
			return true;
		}
		n	+=	4;
		if ((n >= max_nonce) || work_restart[thr_id].restart) {
			*hashes_done = n;
			break;
		}
	}
	return false;
}


#define blkcpy(dest, src, len)\
{\
	__m128i * D = (__m128i *)dest;\
	__m128i * S = (__m128i *)src;\
	size_t i;\
	__m128i aa,bb,cc,dd;\
	\
	for (i = 0; i < (len / 16); i+=4){\
		aa	=	_mm_load_si128(&S[i+0]);\
		bb	=	_mm_load_si128(&S[i+1]);\
		cc	=	_mm_load_si128(&S[i+2]);\
		dd	=	_mm_load_si128(&S[i+3]);\
		\
		_mm_store_si128(&D[i+0], aa);\
		_mm_store_si128(&D[i+1], bb);\
		_mm_store_si128(&D[i+2], cc);\
		_mm_store_si128(&D[i+3], dd);\
	}\
}\

#define blkxor(dest, src, len) \
{\
	__m128i * D = (__m128i *)dest;\
	__m128i * S = (__m128i *)src;\
	size_t i;\
	__m128i aa,bb,cc,dd,ee,ff,gg,hh;\
\
	for (i = 0; i < (len / 16); i+=4){\
		aa	=	_mm_load_si128(&S[i+0]);\
		bb	=	_mm_load_si128(&S[i+1]);\
		cc	=	_mm_load_si128(&S[i+2]);\
		dd	=	_mm_load_si128(&S[i+3]);\
		ee	=	_mm_load_si128(&D[i+0]);\
		ff	=	_mm_load_si128(&D[i+1]);\
		gg	=	_mm_load_si128(&D[i+2]);\
		hh	=	_mm_load_si128(&D[i+3]);\
		ee = _mm_xor_si128(ee, aa);\
		ff = _mm_xor_si128(ff, bb);\
		gg = _mm_xor_si128(gg, cc);\
		hh = _mm_xor_si128(hh, dd);\
		_mm_store_si128(&D[i+0], ee);\
		_mm_store_si128(&D[i+1], ff);\
		_mm_store_si128(&D[i+2], gg);\
		_mm_store_si128(&D[i+3], hh);\
	}\
}\

void 
__attribute__ ((always_inline))
salsa20_8_sse(__m128i *B)
{
	__m128i X0, X1, X2, X3;
	__m128i Y0, Y1, Y2, Y3;
	__m128i Z0, Z1, Z2, Z3;
	__m128i W0, W1, W2, W3;
	
	__m128i T;
	__m128i Y;
	__m128i U;
	__m128i I;
	size_t i;

	X0 = B[ 0];
	X1 = B[ 1];
	X2 = B[ 2];
	X3 = B[ 3];

	Y0 = B[ 4];
	Y1 = B[ 5];
	Y2 = B[ 6];
	Y3 = B[ 7];

	Z0 = B[ 8];
	Z1 = B[ 9];
	Z2 = B[10];
	Z3 = B[11];
/*
	W0 = B[12];
	W1 = B[13];
	W2 = B[14];
	W3 = B[15];
*/
#define step_sse_2(a,b,c, d,e,f, g,h,t, j,k,l, z) \
{ \
	T = _mm_add_epi32(a, b); \
	Y = _mm_add_epi32(d, e); \
	U = _mm_add_epi32(g, h); \
	T = _mm_xor_si128(_mm_slli_epi32(T, z), _mm_srli_epi32(T, (32-z))); \
	Y = _mm_xor_si128(_mm_slli_epi32(Y, z), _mm_srli_epi32(Y, (32-z))); \
	U = _mm_xor_si128(_mm_slli_epi32(U, z), _mm_srli_epi32(U, (32-z))); \
	c = _mm_xor_si128(c, T); \
	f = _mm_xor_si128(f, Y); \
	t = _mm_xor_si128(t, U); \
}

#define step_sse_3(a,b,c, d,e,f, g,h,t, j,k,l, z) \
{ \
	T = _mm_add_epi32(a, b); \
	Y = _mm_add_epi32(d, e); \
	U = _mm_add_epi32(g, h); \
	I = _mm_add_epi32(j, k); \
	T = _mm_xor_si128(_mm_slli_epi32(T, z), _mm_srli_epi32(T, (32-z))); \
	Y = _mm_xor_si128(_mm_slli_epi32(Y, z), _mm_srli_epi32(Y, (32-z))); \
	U = _mm_xor_si128(_mm_slli_epi32(U, z), _mm_srli_epi32(U, (32-z))); \
	I = _mm_xor_si128(_mm_slli_epi32(I, z), _mm_srli_epi32(I, (32-z))); \
	c = _mm_xor_si128(c, T); \
	f = _mm_xor_si128(f, Y); \
	t = _mm_xor_si128(t, U); \
	l = _mm_xor_si128(l, I); \
}



//	for (i = 0; i < 8; i += 2)
	{
		/* Operate on "columns". */

		step_sse_2(X0,X3,X1, Y0,Y3,Y1, Z0,Z3,Z1, W0,W3,W1, 7);
		step_sse_2(X1,X0,X2, Y1,Y0,Y2, Z1,Z0,Z2, W1,W0,W2, 9);
		step_sse_2(X2,X1,X3, Y2,Y1,Y3, Z2,Z1,Z3, W2,W1,W3, 13);
		step_sse_2(X3,X2,X0, Y3,Y2,Y0, Z3,Z2,Z0, W3,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x93); Y1 = _mm_shuffle_epi32(Y1, 0x93); Z1 = _mm_shuffle_epi32(Z1, 0x93);// W1 = _mm_shuffle_epi32(W1, 0x93);
		X3 = _mm_shuffle_epi32(X3, 0x39); Y3 = _mm_shuffle_epi32(Y3, 0x39); Z3 = _mm_shuffle_epi32(Z3, 0x39);// W3 = _mm_shuffle_epi32(W3, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E);// W2 = _mm_shuffle_epi32(W2, 0x4E);

		/* Operate on "rows". */
		step_sse_2(X0,X1,X3, Y0,Y1,Y3, Z0,Z1,Z3, W0,W1,W3, 7);
		step_sse_2(X3,X0,X2, Y3,Y0,Y2, Z3,Z0,Z2, W3,W0,W2, 9);
		step_sse_2(X2,X3,X1, Y2,Y3,Y1, Z2,Z3,Z1, W2,W3,W1, 13);
		step_sse_2(X1,X2,X0, Y1,Y2,Y0, Z1,Z2,Z0, W1,W2,W0, 18);

		/* Rearrange data. */
		X3 = _mm_shuffle_epi32(X3, 0x93); Y3 = _mm_shuffle_epi32(Y3, 0x93); Z3 = _mm_shuffle_epi32(Z3, 0x93);// W3 = _mm_shuffle_epi32(W3, 0x93);
		X1 = _mm_shuffle_epi32(X1, 0x39); Y1 = _mm_shuffle_epi32(Y1, 0x39); Z1 = _mm_shuffle_epi32(Z1, 0x39);// W1 = _mm_shuffle_epi32(W1, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E);// W2 = _mm_shuffle_epi32(W2, 0x4E);
		/* Operate on "columns". */

		step_sse_2(X0,X3,X1, Y0,Y3,Y1, Z0,Z3,Z1, W0,W3,W1, 7);
		step_sse_2(X1,X0,X2, Y1,Y0,Y2, Z1,Z0,Z2, W1,W0,W2, 9);
		step_sse_2(X2,X1,X3, Y2,Y1,Y3, Z2,Z1,Z3, W2,W1,W3, 13);
		step_sse_2(X3,X2,X0, Y3,Y2,Y0, Z3,Z2,Z0, W3,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x93); Y1 = _mm_shuffle_epi32(Y1, 0x93); Z1 = _mm_shuffle_epi32(Z1, 0x93);// W1 = _mm_shuffle_epi32(W1, 0x93);
		X3 = _mm_shuffle_epi32(X3, 0x39); Y3 = _mm_shuffle_epi32(Y3, 0x39); Z3 = _mm_shuffle_epi32(Z3, 0x39);// W3 = _mm_shuffle_epi32(W3, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E);// W2 = _mm_shuffle_epi32(W2, 0x4E);

		/* Operate on "rows". */
		step_sse_2(X0,X1,X3, Y0,Y1,Y3, Z0,Z1,Z3, W0,W1,W3, 7);
		step_sse_2(X3,X0,X2, Y3,Y0,Y2, Z3,Z0,Z2, W3,W0,W2, 9);
		step_sse_2(X2,X3,X1, Y2,Y3,Y1, Z2,Z3,Z1, W2,W3,W1, 13);
		step_sse_2(X1,X2,X0, Y1,Y2,Y0, Z1,Z2,Z0, W1,W2,W0, 18);

		/* Rearrange data. */
		X3 = _mm_shuffle_epi32(X3, 0x93); Y3 = _mm_shuffle_epi32(Y3, 0x93); Z3 = _mm_shuffle_epi32(Z3, 0x93);// W3 = _mm_shuffle_epi32(W3, 0x93);
		X1 = _mm_shuffle_epi32(X1, 0x39); Y1 = _mm_shuffle_epi32(Y1, 0x39); Z1 = _mm_shuffle_epi32(Z1, 0x39);// W1 = _mm_shuffle_epi32(W1, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E);// W2 = _mm_shuffle_epi32(W2, 0x4E);
		/* Operate on "columns". */

		step_sse_2(X0,X3,X1, Y0,Y3,Y1, Z0,Z3,Z1, W0,W3,W1, 7);
		step_sse_2(X1,X0,X2, Y1,Y0,Y2, Z1,Z0,Z2, W1,W0,W2, 9);
		step_sse_2(X2,X1,X3, Y2,Y1,Y3, Z2,Z1,Z3, W2,W1,W3, 13);
		step_sse_2(X3,X2,X0, Y3,Y2,Y0, Z3,Z2,Z0, W3,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x93); Y1 = _mm_shuffle_epi32(Y1, 0x93); Z1 = _mm_shuffle_epi32(Z1, 0x93);// W1 = _mm_shuffle_epi32(W1, 0x93);
		X3 = _mm_shuffle_epi32(X3, 0x39); Y3 = _mm_shuffle_epi32(Y3, 0x39); Z3 = _mm_shuffle_epi32(Z3, 0x39);// W3 = _mm_shuffle_epi32(W3, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E);// W2 = _mm_shuffle_epi32(W2, 0x4E);

		/* Operate on "rows". */
		step_sse_2(X0,X1,X3, Y0,Y1,Y3, Z0,Z1,Z3, W0,W1,W3, 7);
		step_sse_2(X3,X0,X2, Y3,Y0,Y2, Z3,Z0,Z2, W3,W0,W2, 9);
		step_sse_2(X2,X3,X1, Y2,Y3,Y1, Z2,Z3,Z1, W2,W3,W1, 13);
		step_sse_2(X1,X2,X0, Y1,Y2,Y0, Z1,Z2,Z0, W1,W2,W0, 18);

		/* Rearrange data. */
		X3 = _mm_shuffle_epi32(X3, 0x93); Y3 = _mm_shuffle_epi32(Y3, 0x93); Z3 = _mm_shuffle_epi32(Z3, 0x93);// W3 = _mm_shuffle_epi32(W3, 0x93);
		X1 = _mm_shuffle_epi32(X1, 0x39); Y1 = _mm_shuffle_epi32(Y1, 0x39); Z1 = _mm_shuffle_epi32(Z1, 0x39);// W1 = _mm_shuffle_epi32(W1, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E);// W2 = _mm_shuffle_epi32(W2, 0x4E);
		/* Operate on "columns". */

		step_sse_2(X0,X3,X1, Y0,Y3,Y1, Z0,Z3,Z1, W0,W3,W1, 7);
		step_sse_2(X1,X0,X2, Y1,Y0,Y2, Z1,Z0,Z2, W1,W0,W2, 9);
		step_sse_2(X2,X1,X3, Y2,Y1,Y3, Z2,Z1,Z3, W2,W1,W3, 13);
		step_sse_2(X3,X2,X0, Y3,Y2,Y0, Z3,Z2,Z0, W3,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x93); Y1 = _mm_shuffle_epi32(Y1, 0x93); Z1 = _mm_shuffle_epi32(Z1, 0x93);// W1 = _mm_shuffle_epi32(W1, 0x93);
		X3 = _mm_shuffle_epi32(X3, 0x39); Y3 = _mm_shuffle_epi32(Y3, 0x39); Z3 = _mm_shuffle_epi32(Z3, 0x39);// W3 = _mm_shuffle_epi32(W3, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E);// W2 = _mm_shuffle_epi32(W2, 0x4E);

		/* Operate on "rows". */
		step_sse_2(X0,X1,X3, Y0,Y1,Y3, Z0,Z1,Z3, W0,W1,W3, 7);
		step_sse_2(X3,X0,X2, Y3,Y0,Y2, Z3,Z0,Z2, W3,W0,W2, 9);
		step_sse_2(X2,X3,X1, Y2,Y3,Y1, Z2,Z3,Z1, W2,W3,W1, 13);
		step_sse_2(X1,X2,X0, Y1,Y2,Y0, Z1,Z2,Z0, W1,W2,W0, 18);

		/* Rearrange data. */
		X3 = _mm_shuffle_epi32(X3, 0x93); Y3 = _mm_shuffle_epi32(Y3, 0x93); Z3 = _mm_shuffle_epi32(Z3, 0x93);// W3 = _mm_shuffle_epi32(W3, 0x93);
		X1 = _mm_shuffle_epi32(X1, 0x39); Y1 = _mm_shuffle_epi32(Y1, 0x39); Z1 = _mm_shuffle_epi32(Z1, 0x39);// W1 = _mm_shuffle_epi32(W1, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E);// W2 = _mm_shuffle_epi32(W2, 0x4E);
	}
#undef step_sse
#undef step_sse_2

	B[ 0] = _mm_add_epi32(B[ 0], X0);
	B[ 1] = _mm_add_epi32(B[ 1], X1);
	B[ 2] = _mm_add_epi32(B[ 2], X2);
	B[ 3] = _mm_add_epi32(B[ 3], X3);

	B[ 4] = _mm_add_epi32(B[ 4], Y0);
	B[ 5] = _mm_add_epi32(B[ 5], Y1);
	B[ 6] = _mm_add_epi32(B[ 6], Y2);
	B[ 7] = _mm_add_epi32(B[ 7], Y3);

	B[ 8] = _mm_add_epi32(B[ 8], Z0);
	B[ 9] = _mm_add_epi32(B[ 9], Z1);
	B[10] = _mm_add_epi32(B[10], Z2);
	B[11] = _mm_add_epi32(B[11], Z3);

/*	B[12] = _mm_add_epi32(B[12], W0);
	B[13] = _mm_add_epi32(B[13], W1);
	B[14] = _mm_add_epi32(B[14], W2);
	B[15] = _mm_add_epi32(B[15], W3);
*/
}

void salsa20_8_sse_step2(__m128i *B, __m128i *Bx);


void
__attribute__ ((always_inline))
salsa20_8_sse_step1(__m128i *B, __m128i *Bx)
{
	__m128i X0, X1, X2, X3;
	__m128i Y0, Y1, Y2, Y3;
	__m128i Z0, Z1, Z2, Z3;
	__m128i W0, W1, W2, W3;
	
	__m128i T;
	__m128i Y;
	__m128i U;
	__m128i I;
	size_t i;
	
	X0 = (B[ 0] = _mm_xor_si128(B[ 0],Bx[ 0]));
	X1 = (B[ 1] = _mm_xor_si128(B[ 1],Bx[ 1]));
	X2 = (B[ 2] = _mm_xor_si128(B[ 2],Bx[ 2]));
	X3 = (B[ 3] = _mm_xor_si128(B[ 3],Bx[ 3]));
	Y0 = (B[ 4] = _mm_xor_si128(B[ 4],Bx[ 4]));
	Y1 = (B[ 5] = _mm_xor_si128(B[ 5],Bx[ 5]));
	Y2 = (B[ 6] = _mm_xor_si128(B[ 6],Bx[ 6]));
	Y3 = (B[ 7] = _mm_xor_si128(B[ 7],Bx[ 7]));
	Z0 = (B[ 8] = _mm_xor_si128(B[ 8],Bx[ 8]));
	Z1 = (B[ 9] = _mm_xor_si128(B[ 9],Bx[ 9]));
	Z2 = (B[10] = _mm_xor_si128(B[10],Bx[10]));
	Z3 = (B[11] = _mm_xor_si128(B[11],Bx[11]));
	W0 = (B[12] = _mm_xor_si128(B[12],Bx[12]));
	W0 = (B[12] = _mm_xor_si128(B[12],Bx[12]));
	W1 = (B[13] = _mm_xor_si128(B[13],Bx[13]));
	W1 = (B[13] = _mm_xor_si128(B[13],Bx[13]));
	W2 = (B[14] = _mm_xor_si128(B[14],Bx[14]));
	W2 = (B[14] = _mm_xor_si128(B[14],Bx[14]));
	W3 = (B[15] = _mm_xor_si128(B[15],Bx[15]));
	W3 = (B[15] = _mm_xor_si128(B[15],Bx[15]));

#define step_sse_2(a,b,c, d,e,f, g,h,t, j,k,l, z) \
{ \
	T = _mm_add_epi32(a, b); \
	Y = _mm_add_epi32(d, e); \
	U = _mm_add_epi32(g, h); \
	I = _mm_add_epi32(j, k); \
	T = _mm_xor_si128(_mm_slli_epi32(T, z), _mm_srli_epi32(T, (32-z))); \
	Y = _mm_xor_si128(_mm_slli_epi32(Y, z), _mm_srli_epi32(Y, (32-z))); \
	U = _mm_xor_si128(_mm_slli_epi32(U, z), _mm_srli_epi32(U, (32-z))); \
	I = _mm_xor_si128(_mm_slli_epi32(I, z), _mm_srli_epi32(I, (32-z))); \
	c = _mm_xor_si128(c, T); \
	f = _mm_xor_si128(f, Y); \
	t = _mm_xor_si128(t, U); \
	l = _mm_xor_si128(l, I); \
}


//	for (i = 0; i < 8; i += 4)
	{
		step_sse_2(X0,X3,X1, Y0,Y3,Y1, Z0,Z3,Z1, W0,W3,W1, 7);
		step_sse_2(X1,X0,X2, Y1,Y0,Y2, Z1,Z0,Z2, W1,W0,W2, 9);
		step_sse_2(X2,X1,X3, Y2,Y1,Y3, Z2,Z1,Z3, W2,W1,W3, 13);
		step_sse_2(X3,X2,X0, Y3,Y2,Y0, Z3,Z2,Z0, W3,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x93); Y1 = _mm_shuffle_epi32(Y1, 0x93); Z1 = _mm_shuffle_epi32(Z1, 0x93); W1 = _mm_shuffle_epi32(W1, 0x93);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E); W2 = _mm_shuffle_epi32(W2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x39); Y3 = _mm_shuffle_epi32(Y3, 0x39); Z3 = _mm_shuffle_epi32(Z3, 0x39); W3 = _mm_shuffle_epi32(W3, 0x39);

		step_sse_2(X0,X1,X3, Y0,Y1,Y3, Z0,Z1,Z3, W0,W1,W3, 7);
		step_sse_2(X3,X0,X2, Y3,Y0,Y2, Z3,Z0,Z2, W3,W0,W2, 9);
		step_sse_2(X2,X3,X1, Y2,Y3,Y1, Z2,Z3,Z1, W2,W3,W1, 13);
		step_sse_2(X1,X2,X0, Y1,Y2,Y0, Z1,Z2,Z0, W1,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x39); Y1 = _mm_shuffle_epi32(Y1, 0x39); Z1 = _mm_shuffle_epi32(Z1, 0x39); W1 = _mm_shuffle_epi32(W1, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E); W2 = _mm_shuffle_epi32(W2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x93); Y3 = _mm_shuffle_epi32(Y3, 0x93); Z3 = _mm_shuffle_epi32(Z3, 0x93); W3 = _mm_shuffle_epi32(W3, 0x93);

		
		

		step_sse_2(X0,X3,X1, Y0,Y3,Y1, Z0,Z3,Z1, W0,W3,W1, 7);
		step_sse_2(X1,X0,X2, Y1,Y0,Y2, Z1,Z0,Z2, W1,W0,W2, 9);
		step_sse_2(X2,X1,X3, Y2,Y1,Y3, Z2,Z1,Z3, W2,W1,W3, 13);
		step_sse_2(X3,X2,X0, Y3,Y2,Y0, Z3,Z2,Z0, W3,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x93); Y1 = _mm_shuffle_epi32(Y1, 0x93); Z1 = _mm_shuffle_epi32(Z1, 0x93); W1 = _mm_shuffle_epi32(W1, 0x93);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E); W2 = _mm_shuffle_epi32(W2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x39); Y3 = _mm_shuffle_epi32(Y3, 0x39); Z3 = _mm_shuffle_epi32(Z3, 0x39); W3 = _mm_shuffle_epi32(W3, 0x39);

		step_sse_2(X0,X1,X3, Y0,Y1,Y3, Z0,Z1,Z3, W0,W1,W3, 7);
		step_sse_2(X3,X0,X2, Y3,Y0,Y2, Z3,Z0,Z2, W3,W0,W2, 9);
		step_sse_2(X2,X3,X1, Y2,Y3,Y1, Z2,Z3,Z1, W2,W3,W1, 13);
		step_sse_2(X1,X2,X0, Y1,Y2,Y0, Z1,Z2,Z0, W1,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x39); Y1 = _mm_shuffle_epi32(Y1, 0x39); Z1 = _mm_shuffle_epi32(Z1, 0x39); W1 = _mm_shuffle_epi32(W1, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E); W2 = _mm_shuffle_epi32(W2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x93); Y3 = _mm_shuffle_epi32(Y3, 0x93); Z3 = _mm_shuffle_epi32(Z3, 0x93); W3 = _mm_shuffle_epi32(W3, 0x93);














		step_sse_2(X0,X3,X1, Y0,Y3,Y1, Z0,Z3,Z1, W0,W3,W1, 7);
		step_sse_2(X1,X0,X2, Y1,Y0,Y2, Z1,Z0,Z2, W1,W0,W2, 9);
		step_sse_2(X2,X1,X3, Y2,Y1,Y3, Z2,Z1,Z3, W2,W1,W3, 13);
		step_sse_2(X3,X2,X0, Y3,Y2,Y0, Z3,Z2,Z0, W3,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x93); Y1 = _mm_shuffle_epi32(Y1, 0x93); Z1 = _mm_shuffle_epi32(Z1, 0x93); W1 = _mm_shuffle_epi32(W1, 0x93);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E); W2 = _mm_shuffle_epi32(W2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x39); Y3 = _mm_shuffle_epi32(Y3, 0x39); Z3 = _mm_shuffle_epi32(Z3, 0x39); W3 = _mm_shuffle_epi32(W3, 0x39);

		step_sse_2(X0,X1,X3, Y0,Y1,Y3, Z0,Z1,Z3, W0,W1,W3, 7);
		step_sse_2(X3,X0,X2, Y3,Y0,Y2, Z3,Z0,Z2, W3,W0,W2, 9);
		step_sse_2(X2,X3,X1, Y2,Y3,Y1, Z2,Z3,Z1, W2,W3,W1, 13);
		step_sse_2(X1,X2,X0, Y1,Y2,Y0, Z1,Z2,Z0, W1,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x39); Y1 = _mm_shuffle_epi32(Y1, 0x39); Z1 = _mm_shuffle_epi32(Z1, 0x39); W1 = _mm_shuffle_epi32(W1, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E); W2 = _mm_shuffle_epi32(W2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x93); Y3 = _mm_shuffle_epi32(Y3, 0x93); Z3 = _mm_shuffle_epi32(Z3, 0x93); W3 = _mm_shuffle_epi32(W3, 0x93);

		
		

		step_sse_2(X0,X3,X1, Y0,Y3,Y1, Z0,Z3,Z1, W0,W3,W1, 7);
		step_sse_2(X1,X0,X2, Y1,Y0,Y2, Z1,Z0,Z2, W1,W0,W2, 9);
		step_sse_2(X2,X1,X3, Y2,Y1,Y3, Z2,Z1,Z3, W2,W1,W3, 13);
		step_sse_2(X3,X2,X0, Y3,Y2,Y0, Z3,Z2,Z0, W3,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x93); Y1 = _mm_shuffle_epi32(Y1, 0x93); Z1 = _mm_shuffle_epi32(Z1, 0x93); W1 = _mm_shuffle_epi32(W1, 0x93);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E); W2 = _mm_shuffle_epi32(W2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x39); Y3 = _mm_shuffle_epi32(Y3, 0x39); Z3 = _mm_shuffle_epi32(Z3, 0x39); W3 = _mm_shuffle_epi32(W3, 0x39);

		step_sse_2(X0,X1,X3, Y0,Y1,Y3, Z0,Z1,Z3, W0,W1,W3, 7);
		step_sse_2(X3,X0,X2, Y3,Y0,Y2, Z3,Z0,Z2, W3,W0,W2, 9);
		step_sse_2(X2,X3,X1, Y2,Y3,Y1, Z2,Z3,Z1, W2,W3,W1, 13);
		step_sse_2(X1,X2,X0, Y1,Y2,Y0, Z1,Z2,Z0, W1,W2,W0, 18);

		X1 = _mm_shuffle_epi32(X1, 0x39); Y1 = _mm_shuffle_epi32(Y1, 0x39); Z1 = _mm_shuffle_epi32(Z1, 0x39); W1 = _mm_shuffle_epi32(W1, 0x39);
		X2 = _mm_shuffle_epi32(X2, 0x4E); Y2 = _mm_shuffle_epi32(Y2, 0x4E); Z2 = _mm_shuffle_epi32(Z2, 0x4E); W2 = _mm_shuffle_epi32(W2, 0x4E);
		X3 = _mm_shuffle_epi32(X3, 0x93); Y3 = _mm_shuffle_epi32(Y3, 0x93); Z3 = _mm_shuffle_epi32(Z3, 0x93); W3 = _mm_shuffle_epi32(W3, 0x93);
	}
#undef step_sse
#undef step_sse_2

	B[ 0] = _mm_add_epi32(B[ 0], X0);
	B[ 1] = _mm_add_epi32(B[ 1], X1);
	B[ 2] = _mm_add_epi32(B[ 2], X2);
	B[ 3] = _mm_add_epi32(B[ 3], X3);

	B[ 4] = _mm_add_epi32(B[ 4], Y0);
	B[ 5] = _mm_add_epi32(B[ 5], Y1);
	B[ 6] = _mm_add_epi32(B[ 6], Y2);
	B[ 7] = _mm_add_epi32(B[ 7], Y3);

	B[ 8] = _mm_add_epi32(B[ 8], Z0);
	B[ 9] = _mm_add_epi32(B[ 9], Z1);
	B[10] = _mm_add_epi32(B[10], Z2);
	B[11] = _mm_add_epi32(B[11], Z3);

	B[12] = _mm_add_epi32(B[12], W0);
	B[13] = _mm_add_epi32(B[13], W1);
	B[14] = _mm_add_epi32(B[14], W2);
	B[15] = _mm_add_epi32(B[15], W3);
}


void
smix(uint32_t * B, size_t r, uint64_t N, void * V, void * XY)
{
//	__m128i *X = (__m128i *)XY;
//	__m128i *X_= (__m128i *)XY + 32;
	__m128i X [32];
	__m128i X_[32];
	
	uint32_t * X32 = (uint32_t *)X;
	uint32_t * X32_ = (uint32_t *)X_;
	uint64_t i, j;
	size_t k;

	/* 1: X <-- B */
	for (k = 0; k < 2 * 3; k++) {
		for (i = 0; i < 16; i++) {
			X32_[k * 16 + i] = B[(k * 16 + (i * 5 % 16))];
		}
	}

	X[0]	=	X_[0];
	X[1]	=	X_[1];
	X[2]	=	X_[2];
	X[3]	=	X_[3];

	X[4]	=	X_[8+0];
	X[5]	=	X_[8+1];
	X[6]	=	X_[8+2];
	X[7]	=	X_[8+3];

	X[8]	=	X_[16+0];
	X[9]	=	X_[16+1];
	X[10]	=	X_[16+2];
	X[11]	=	X_[16+3];

/*	X[12]	=	X_[24+0];
	X[13]	=	X_[24+1];
	X[14]	=	X_[24+2];
	X[15]	=	X_[24+3];
*/
	X[16-4]	=	X_[4+0];
	X[17-4]	=	X_[4+1];
	X[18-4]	=	X_[4+2];
	X[19-4]	=	X_[4+3];

	X[20-4]	=	X_[4+8+0];
	X[21-4]	=	X_[4+8+1];
	X[22-4]	=	X_[4+8+2];
	X[23-4]	=	X_[4+8+3];

	X[24-4]	=	X_[4+16+0];
	X[25-4]	=	X_[4+16+1];
	X[26-4]	=	X_[4+16+2];
	X[27-4]	=	X_[4+16+3];
/*
	X[28]	=	X_[4+24+0];
	X[29]	=	X_[4+24+1];
	X[30]	=	X_[4+24+2];
	X[31]	=	X_[4+24+3];
*/
//	memcpy(X32, B, 128*sizeof(unsigned int));
	/* 2: for i = 0 to N - 1 do */
	for (i = 0; i < 1024; i += 1) {
		blkcpy((void *)((unsigned char*)(V) + i * 128 * 3), (void *)X, 128 * 3);
///		blockmix_salsa8_sse(X, Y, X, 1);
		blkxor(&X[0], &X[12], 3*64);
		salsa20_8_sse(&X[0]);
		blkxor(&X[12], &X[0], 3*64);
		salsa20_8_sse(&X[12]);
///		salsa20_8_sse_step1(&X[0], &X[16]);
///		salsa20_8_sse_step1(&X[16], &X[0]);
/*
		blkcpy((void *)((unsigned char*)(V) + (i + 1) * 128 * 4), (void *)X, 128 * 4);

//		blockmix_salsa8_sse(X, Y, X, 1);
///		blkxor(&X[0], &X[16], 4*64);
///		salsa20_8_sse(&X[0]);
///		blkxor(&X[16], &X[0], 4*64);
///		salsa20_8_sse(&X[16]);
		salsa20_8_sse_step1(&X[0], &X[16]);
		salsa20_8_sse_step1(&X[16], &X[0]);
*/
	}
	
	for (i = 0; i < 1024; i += 1) {
		j = (X32[48]&1023);
		blkxor(&X[ 0], (void *)((unsigned char*)(V) + j * 128 * 3 + 0*64), 64);
		blkxor(&X[16-4], (void *)((unsigned char*)(V) + j * 128 * 3 + 0*64 + 3*64), 64);

		j = (X32[48+16]&1023);
		blkxor(&X[ 4], (void *)((unsigned char*)(V) + j * 128 * 3 + 1*64), 64);
		blkxor(&X[20-4], (void *)((unsigned char*)(V) + j * 128 * 3 + 1*64 + 3*64), 64);

		j = (X32[48+32]&1023);
		blkxor(&X[ 8], (void *)((unsigned char*)(V) + j * 128 * 3 + 2*64), 64 * 1);
		blkxor(&X[24-4], (void *)((unsigned char*)(V) + j * 128 * 3 + 2*64 + 3*64), 64 * 1);
/*
		j = (X32[64+48]&1023);
		blkxor(&X[12], (void *)((unsigned char*)(V) + j * 128 * 4 + 3*64), 64 * 1);
		blkxor(&X[28], (void *)((unsigned char*)(V) + j * 128 * 4 + 3*64 + 256), 64 * 1);
*/
		blkxor(&X[0], &X[12], 3*64);
		salsa20_8_sse(&X[0]);

		blkxor(&X[12], &X[0], 3*64);
		salsa20_8_sse(&X[12]);
///		salsa20_8_sse_step1(&X[0], &X[16]);
///		salsa20_8_sse_step1(&X[16],&X[0]);
/*
		j = (X32[64]&1023);
		blkxor(&X[ 0], (void *)((unsigned char*)(V) + j * 128 * 4 + 0*64), 64);
		blkxor(&X[16], (void *)((unsigned char*)(V) + j * 128 * 4 + 0*64 + 256), 64);

		j = (X32[64+16]&1023);
		blkxor(&X[ 4], (void *)((unsigned char*)(V) + j * 128 * 4 + 1*64), 64);
		blkxor(&X[20], (void *)((unsigned char*)(V) + j * 128 * 4 + 1*64 + 256), 64);

		j = (X32[64+32]&1023);
		blkxor(&X[ 8], (void *)((unsigned char*)(V) + j * 128 * 4 + 2*64), 64 * 1);
		blkxor(&X[24], (void *)((unsigned char*)(V) + j * 128 * 4 + 2*64 + 256), 64 * 1);

		j = (X32[64+48]&1023);
		blkxor(&X[12], (void *)((unsigned char*)(V) + j * 128 * 4 + 3*64), 64 * 1);
		blkxor(&X[28], (void *)((unsigned char*)(V) + j * 128 * 4 + 3*64 + 256), 64 * 1);

///		blkxor(&X[0], &X[16], 4*64);
///		salsa20_8_sse(&X[0]);
///		blkxor(&X[16], &X[0], 4*64);
///		salsa20_8_sse(&X[16]);
		salsa20_8_sse_step1(&X[0], &X[16]);
		salsa20_8_sse_step1(&X[16], &X[0]);
*/
	}

//	printf("----\n");
//	print_m128i(X[0]);
//	print_m128i(X[8]);
//	print_m128i(X[16]);
//	print_m128i(X[32]);

	X_[0]		=X[0];
	X_[1]		=X[1];
	X_[2]		=X[2];
	X_[3]		=X[3];

	X_[8+0]		=X[4];
	X_[8+1]		=X[5];	
	X_[8+2]		=X[6];	
	X_[8+3]		=X[7];

	X_[16+0]	=X[8];	
	X_[16+1]	=X[9];	
	X_[16+2]	=X[10];
	X_[16+3]	=X[11];
/*
	X_[24+0]	=X[12];
	X_[24+1]	=X[13];
	X_[24+2]	=X[14];
	X_[24+3]	=X[15];
*/
	X_[4+0]		=X[16-4];
	X_[4+1]		=X[17-4];
	X_[4+2]		=X[18-4];
	X_[4+3]		=X[19-4];

	X_[4+8+0]	=X[20-4];
	X_[4+8+1]	=X[21-4];
	X_[4+8+2]	=X[22-4];
	X_[4+8+3]	=X[23-4];

	X_[4+16+0]	=X[24-4];
	X_[4+16+1]	=X[25-4];
	X_[4+16+2]	=X[26-4];
	X_[4+16+3]	=X[27-4];
/*
	X_[4+24+0]	=X[28];
	X_[4+24+1]	=X[29];
	X_[4+24+2]	=X[30];
	X_[4+24+3]	=X[31];
*/
	/* 10: B' <-- X */
	for (k = 0; k < 2 * 3; k++) {
		for (i = 0; i < 16; i++) {
			B[(k * 16 + (i * 5 % 16))] = X32_[k * 16 + i];
		}
	}
}

/* cpu and memory intensive function to transform a 80 byte buffer into a 32 byte output
   scratchpad size needs to be at least 63 + (128 * r * p) + (256 * r + 64) + (128 * r * N) bytes
 */
uint32_t scrypt_1024_1_1_256_sp2(const char* input, char* output, char* scratchpad)
{
	uint8_t * B;
	
	uint32_t __attribute__((aligned(128))) data[128];
	
	uint32_t * V;
	uint32_t * XY;
	uint32_t i;
	
	uint32_t r1;
	uint32_t r2;
	uint32_t r3;
	uint32_t r4;

	uint32_t rt = ((uint32_t*)output)[0];
	uint32_t *rtp = ((uint32_t*)output);

	const uint32_t N = 1024;
	const uint32_t r = 1;
	const uint32_t p = 1;

	B = (uint8_t *)(((uintptr_t)(scratchpad) + 63) & ~ (uintptr_t)(63));

	XY = (uint32_t *)(scratchpad + 128*1024 );

	V = (uint32_t *)(scratchpad);
	
	/* 1: (B_0 ... B_{p-1}) <-- PBKDF2(P, S, 1, p * MFLen) */
	PBKDF2_SHA256_80_128((uint32_t*)&input[0*80], (uint32_t*)&data[0*32]);
	PBKDF2_SHA256_80_128((uint32_t*)&input[1*80], (uint32_t*)&data[1*32]);
	PBKDF2_SHA256_80_128((uint32_t*)&input[2*80], (uint32_t*)&data[2*32]);
//	PBKDF2_SHA256_80_128((uint32_t*)&input[3*80], (uint32_t*)&data[3*32]);

	/* 3: B_i <-- MF(B_i, N) */
	smix(data, r, N, V, XY);

	/* 5: DK <-- PBKDF2(P, B, 1, dkLen) */
//	printf("%08x\n",((uint32_t*)&B[0*128])[0]);
	r1 = PBKDF2_SHA256_80_128_32((const uint32_t*)&input[0*80], (const uint32_t*)&data[0*32]);
	if(r1<=rt)	return 1;

//	printf("%08x\n",((uint32_t*)&B[1*128])[0]);
	r2 = PBKDF2_SHA256_80_128_32((const uint32_t*)&input[1*80], (const uint32_t*)&data[1*32]);
	if(r2<=rt)	return 2;

//	printf("%08x\n",((uint32_t*)&B[2*128])[0]);
	r3 = PBKDF2_SHA256_80_128_32((const uint32_t*)&input[2*80], (const uint32_t*)&data[2*32]);
	if(r3<=rt)	return 3;

///	r4 = PBKDF2_SHA256_80_128_32((const uint32_t*)&input[3*80], (const uint32_t*)&data[3*32]);
///	if(r4<=rt)	return 4;
	return 0;
}

int scanhash_scrypt2(int thr_id, unsigned char *pdata, unsigned char *scratchbuf,
	const unsigned char *ptarget,
	uint32_t max_nonce, unsigned int *hashes_done)
{
	unsigned char __attribute__((aligned(128))) data[8*80];
	unsigned char __attribute__((aligned(128))) tmp_hash[32+32];
	uint32_t *nonce = (uint32_t *)(data + 64 + 12);
	uint32_t *nonce2 = (uint32_t *)(data + 64 + 12 + 1*80);
	uint32_t *nonce3 = (uint32_t *)(data + 64 + 12 + 2*80);
	uint32_t *nonce4 = (uint32_t *)(data + 64 + 12 + 3*80);
	uint32_t n = 0;
	uint32_t Htarg = *(uint32_t *)(ptarget + 28);
	int i;
	uint32_t ret;
	
//	Htarg++;
	
	for (i = 0; i < 80/4; i++)		((uint32_t *)data)[i] = swab32(((uint32_t *)pdata)[i]);
	for (i = 0; i < 80/4; i++)		((uint32_t *)data)[i+20] = swab32(((uint32_t *)pdata)[i]);
	for (i = 0; i < 80/4; i++)		((uint32_t *)data)[i+40] = swab32(((uint32_t *)pdata)[i]);
///	for (i = 0; i < 80/4; i++)		((uint32_t *)data)[i+60] = swab32(((uint32_t *)pdata)[i]);

	*((uint32_t*)tmp_hash)	=	Htarg;
	n++;
	while(1) {
		*nonce = n;
		*nonce2= (n+1);
		*nonce3= (n+2);
///		*nonce4= (n+3);
		
		ret = scrypt_1024_1_1_256_sp2((const char*)data, (char*)tmp_hash, (char*)scratchbuf);

		if (ret == 1) {
//			printf("0\n");
			*(uint32_t *)(pdata + 64 + 12) = swab32(n);
			*hashes_done = n;
			return true;
		}
		if (ret == 2) {
//			printf("1\n");
			n++;
			*(uint32_t *)(pdata + 64 + 12) = swab32(n);
			*hashes_done = n;
			return true;
		}
		if (ret == 3) {
//			printf("2\n");
			n+=2;
			*(uint32_t *)(pdata + 64 + 12) = swab32(n);
			*hashes_done = n;
			return true;
		}
/**		if (ret == 4) {
			printf("3\n");
			n+=3;
			*(uint32_t *)(pdata + 64 + 12) = swab32(n);
			*hashes_done = n;
			return true;
		}
*/
		n+=3;
		if ((n >= max_nonce) || work_restart[thr_id].restart ) {
//			work_restart[thr_id].restart = 0;
			*hashes_done = n;
			break;
		}
	}
	return false;
}
