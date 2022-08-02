/*
 * MIT License
 *
 * Copyright (c) 2022 Reto Achermann, The University of British Columbia
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * SPDX-License-Identifier: MIT
 */

include "Spec/BitmaskSpec.s.dfy"
include "Spec/BitmaskImplIF.s.dfy"

///
module BitmaskFixedChunks refines BitmaskImplIF {
    ////////////////////////////////////////////////////////////////////////////////
    // Types Definitions
    ////////////////////////////////////////////////////////////////////////////////

    /// The specification of the bitmask. This is the higher-level module
    /// that this module refines.
    import S = BitmaskSpec

    /// declares the type for the bitmask
    type T = seq<seq<bool>>

    const CHUNK_SIZE : nat := 64

    /// conversin of a
    function GetChunk(i: nat) : nat {
        i / CHUNK_SIZE
    }

    function GetChunkOffset(i: nat) : nat {
        i % CHUNK_SIZE
    }

    /// interpretation functions for the Bitmask Type and the number type
    function I(A: T) : (r: S.T)
        //requires Inv(A)
        ensures S.Inv(r)
    {
        seq(|A| * CHUNK_SIZE, i requires 0 <= i < |A|*CHUNK_SIZE => A[GetChunk(i)][GetChunkOffset(i)])
    }

    lemma IResult(A: T, i: nat)
        requires 0 <= i < |A|*CHUNK_SIZE
        requires Inv(A)
        ensures I(A)[i] == A[GetChunk(i)][GetChunkOffset(i)]
    {
    }

    lemma IEqual(A: T, B: T)
        requires Inv(A) && Inv(B)
        ensures A == B <==>  I(A) == I(B)
    {
        if A == B {
            assert forall i | 0 <= i < |I(A)| :: I(A)[i] == I(B)[i];
            assert forall i | 0 <= i < |I(A)| :: I(A)[i] == A[GetChunk(i)][GetChunkOffset(i)];
            assert forall i | 0 <= i < |I(B)| :: I(B)[i] == B[GetChunk(i)][GetChunkOffset(i)];
            assert forall i | 0 <= i < |I(A)| :: A[GetChunk(i)][GetChunkOffset(i)] == B[GetChunk(i)][GetChunkOffset(i)];
            assert |A| == |B|;
            assert forall i | 0 <= i < |A| :: |A[i]| == |B[i]|;
            assert forall i | 0 <= i < |A| :: |A[i]| == CHUNK_SIZE;
            assert forall i, j | 0 <= i < |A| && 0 <= j < CHUNK_SIZE :: A[i][j] == I(A)[i * 64 + j];
            assert forall i | 0 <= i < |A| :: A[i] == B[i];
        } else {
            if |A| == |B| {
                assert |I(A)| == |I(B)|;
                assert exists i | 0 <= i < |A| :: A[i] != B[i];
                var di :| 0 <= di < |A| &&  A[di] != B[di];
                assert A[di] != B[di];
                assert exists i | 0 <= i < CHUNK_SIZE :: A[di][i] != B[di][i];
                var dj :| 0 <= dj < CHUNK_SIZE &&  A[di][dj] != B[di][dj];
                assert I(A)[di * CHUNK_SIZE + dj] != I(B)[di * CHUNK_SIZE + dj];
                assert exists i | 0 <= i < |A| * CHUNK_SIZE :: I(A)[i] != I(B)[i];
                assert I(A) != I(B);
            } else {
                assert |I(A)| != |I(B)|;
            }
        }
    }

    // simple function to flatten the bitmask representation
    function Flatten(A: T) : seq<bool> {
        if |A| == 0 then []
        else A[0] + Flatten(A[1..])
    }

    lemma lemma_FLattenIsI(A: T)
        requires Inv(A)
        ensures Flatten(A) == I(A)
    {
        if |A| == 0 {
        } else {
            lemma_FLattenIsI(A[1..]);
            assert Flatten(A) == A[0] + Flatten(A[1..]);
            assert I(A) == seq(CHUNK_SIZE, i requires 0 <= i < CHUNK_SIZE => A[0][GetChunkOffset(i)]) + I(A[1..]);
        }
    }

    lemma lemma_IStep(A:T)
        requires Inv(A)
        requires |A| > 0
        ensures I(A) == A[0] + I(A[1..])
    {
    }

    /// invariant, must implie the abstract invariant
    predicate Inv(A: T) {
        forall i | 0 <= i < |A| :: |A[i]| == CHUNK_SIZE
    }



    /// whether or not the size parameter is valid, her
    predicate ValidSize(n: nat)
        ensures  ValidSize(n) ==> S.ValidSize(n)
    {
        // we just handle multiples of 64 bit for now
        n % CHUNK_SIZE == 0
    }


    ////////////////////////////////////////////////////////////////////////////////
    // Constructor Functions
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_new_zeros(M: nat) : (r: T)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_zeros(r)
        ensures I(r) == S.bitmask_new_zeros(M)
    {
        S.reveal_bitmask_new_zeros();

        var nchunks := (M / CHUNK_SIZE);
        seq(nchunks, i => seq(CHUNK_SIZE, j => false))
    }

    function bitmask_new_ones(M: nat) : (r: T)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_ones(r)
        ensures I(r) == S.bitmask_new_ones(M)
    {
        S.reveal_bitmask_new_ones();

        var nchunks := (M / CHUNK_SIZE);
        seq(nchunks, i => seq(CHUNK_SIZE, j => true))
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Bit Counts
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_nbits(A: T) : (r: nat)
        // requires Inv(A)
        ensures r == S.bitmask_nbits(I(A))
    {
        |A| * CHUNK_SIZE
    }

    function bitmask_popcnt_chunk(A: seq<bool>) : (r: nat)
        ensures r == S.bitmask_popcnt(A)
    {
        S.reveal_bitmask_popcnt();
        if |A| == 0 then 0
        else (if A[0] then 1 else 0) + bitmask_popcnt_chunk(A[1..])
    }

    function bitmask_popcnt(A: T) : (r: nat)
        //requires Inv(A)
        ensures r <= bitmask_nbits(A)
        ensures r == S.bitmask_popcnt(I(A))
    {
        S.reveal_bitmask_popcnt();
        if |A| == 0 then 0
        else
            var r := bitmask_popcnt(A[1..]);
            assert I(A) == I(A[..1]) + I(A[1..]);
            assert A == A[..1] + A[1..];
            assert S.bitmask_popcnt(I(A)) == S.bitmask_popcnt(I(A[..1])) + S.bitmask_popcnt(I(A[1..])) by {
                S.PopcntDist(I(A[..1]), I(A[1..]));
            }
            assert r == S.bitmask_popcnt(I(A[1..]));
            assert I(A[..1]) == A[0];
            assert S.bitmask_popcnt(I(A[..1])) == bitmask_popcnt_chunk(A[0]);
            bitmask_popcnt_chunk(A[0]) + r
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Bitwise Get/Set Operations
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_get_bit(A: T, i: nat) : (r: bool)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures r == S.bitmask_get_bit(I(A), i);
    {
        A[GetChunk(i)][GetChunkOffset(i)]
    }

    function bitmask_set_bit(A: T, i: nat) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures I(r) == S.bitmask_set_bit(I(A), i);
    {
        var c := GetChunk(i);
        var o := GetChunkOffset(i);

        var chumk := A[c];
        A[c := chumk[o := true]]
    }

    function bitmask_clear_bit(A: T, i: nat) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures I(r) == S.bitmask_clear_bit(I(A), i);
    {
        var c := GetChunk(i);
        var o := GetChunkOffset(i);

        var chumk := A[c];
        A[c := chumk[o := false]]
    }

    function bitmask_toggle_bit(A: T, i: nat) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures I(r) == S.bitmask_toggle_bit(I(A), i);
    {
        var c := GetChunk(i);
        var o := GetChunkOffset(i);

        var chumk := A[c];
        A[c := chumk[o := !chumk[o]]]
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Predicates
    ////////////////////////////////////////////////////////////////////////////////


    predicate bitmask_eq(A: T, B: T)
        // requires Inv(A) && Inv(B)
        ensures bitmask_eq(A, B) <==> A == B
        ensures bitmask_eq(A, B) <==> S.bitmask_eq(I(A), I(B))
    {
        IEqual(A, B);
        A == B
    }

    predicate bitmask_is_zeros(A: T)
        // requires Inv(A)
        ensures bitmask_is_zeros(A) <==> S.bitmask_is_zeros(I(A))
    {
        S.reveal_bitmask_is_zeros();
        assert forall i, j | 0 <= i < |A| && 0 <= j < CHUNK_SIZE :: A[i][j] == I(A)[i * CHUNK_SIZE + j];
        forall i, j | 0 <= i < |A| && 0 <= j < CHUNK_SIZE :: !A[i][j]
    }

    predicate bitmask_is_ones(A: T)
        // requires Inv(A)
        ensures bitmask_is_ones(A) <==> S.bitmask_is_ones(I(A))
    {
        S.reveal_bitmask_is_ones();
        assert forall i, j | 0 <= i < |A| && 0 <= j < CHUNK_SIZE :: A[i][j] == I(A)[i * CHUNK_SIZE + j];
        forall i | 0 <= i < |A| * CHUNK_SIZE :: A[GetChunk(i)][GetChunkOffset(i)]
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Operations
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_and(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures I(r) == S.bitmask_and(I(A), I(B))
    {
        S.reveal_bitmask_and();
        seq(|A|, i requires 0 <= i < |A| => seq(CHUNK_SIZE, j requires 0 <= j < CHUNK_SIZE => A[i][j] && B[i][j]))
    }

    function bitmask_or(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures I(r) == S.bitmask_or(I(A), I(B))
    {
        S.reveal_bitmask_or();
        seq(|A|, i requires 0 <= i < |A| => seq(CHUNK_SIZE, j requires 0 <= j < CHUNK_SIZE => A[i][j] || B[i][j]))
    }

    function bitmask_xor(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures I(r) == S.bitmask_xor(I(A), I(B))
    {
        S.reveal_bitmask_xor();
        seq(|A|, i requires 0 <= i < |A| => seq(CHUNK_SIZE, j requires 0 <= j < CHUNK_SIZE => A[i][j] != B[i][j]))
    }

    function bitmask_not(A: T) : (r: T)
        // requires Inv(A)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures I(r) == S.bitmask_not(I(A))
    {
        S.reveal_bitmask_not();
        seq(|A|, i requires 0 <= i < |A| => seq(CHUNK_SIZE, j requires 0 <= j < CHUNK_SIZE => !A[i][j]))
    }
}
