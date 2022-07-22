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

include "BitmaskIF.s.dfy"


/// Bitmask Specification
///
/// This module contains the trusted, mathematical specification of the bitmask
/// implementation. The specification models the bitmask as a sequence of bits,
/// and defines operations (and, or, ...) on it.
///
/// Note, this should be the only implementing module that directly refines
/// from BitmaskIF.
module BitmaskSpec refines BitmaskIF {

    ////////////////////////////////////////////////////////////////////////////////
    // Types Definitions
    ////////////////////////////////////////////////////////////////////////////////


    /// The type of the bitmask.
    /// Here we just use a sequence of booleans representing the bitmask's bits.
    type T = seq<bool>

    /// converts the type R to a nat
    function ToNat(n: nat) : nat { n }

    /// the invariant
    predicate Inv(A: T) { true }

    /// whether the number of bits is supported
    predicate ValidSize(n: nat) { true }

    /// Predicate whether the bit `i` is valid for the bitmask `A`
    predicate ValidBit(A: T, i: nat) {
        i < |A|
    }

    /// converts the bitmask type to a sequence of booleans
    function ToBitSeq(A: T) : seq<bool> {
        A
    }


    ////////////////////////////////////////////////////////////////////////////////
    // Constructor Functions
    ////////////////////////////////////////////////////////////////////////////////


    function {:opaque} bitmask_new_zeros(M: nat) : (r: T)
        // requires ValidSize(M)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_zeros(r)
    {
        reveal_bitmask_is_zeros();
        seq(M, i => false)
    }

    function {:opaque} bitmask_new_ones(M: nat) : (r: T)
        // requires ValidSize(M)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_ones(r)

    {
        reveal_bitmask_is_ones();
        seq(M, i => true)
    }

    // some concatenation function
    function bitmask_concat(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A) + bitmask_nbits(B)
        ensures ToBitSeq(r) == ToBitSeq(A) + ToBitSeq(B)
    {
        A + B
    }

    function bitmask_split(A: T, i: nat) : (r:(T, T))
        // requires Inv(A)
        // requires i <= bitmask_nbits(A)
        ensures Inv(r.0) && Inv(r.1 )
        ensures ToBitSeq(A) == ToBitSeq(r.0) + ToBitSeq(r.1)
    {
        (A[..i], A[i..])
    }

    lemma lemma_bitmask_split_concat(A: T, B: T, i: nat)
        // requires Inv(A) && Inv(B)
        ensures A == bitmask_split(bitmask_concat(A, B), bitmask_nbits(A)).0
        ensures B == bitmask_split(bitmask_concat(A, B), bitmask_nbits(A)).1
    {

    }


    ////////////////////////////////////////////////////////////////////////////////
    // Bit Counts
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_nbits(A: T) : (r: nat)
        // requires Inv(A)
    {
        |A|
    }

    function {:opaque} bitmask_popcnt(A: T) : (r: nat)
        // requires Inv(A)
    {
        if |A| == 0 then 0
        else (if A[0] then 1 else 0) + bitmask_popcnt(A[1..])
    }

    lemma PopcntDist(A: T, B: T)
        ensures bitmask_popcnt(A + B) == bitmask_popcnt(A) + bitmask_popcnt(B)
    {
        reveal_bitmask_popcnt();
        if |A| == 0 {
            assert A + B == B;
            assert bitmask_popcnt(A + B) == bitmask_popcnt(B);
        } else {
            PopcntDist(A[1..], B);
            assert A + B == [A[0]] + (A[1..] + B);
        }
    }


    ////////////////////////////////////////////////////////////////////////////////
    // Bitwise Get/Set Operations
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_get_bit(A: T, i: nat) : (r: bool)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
    {
        A[i]
    }

    function bitmask_set_bit(A: T, i: nat) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
    {
        A[i := true]
    }

    function bitmask_clear_bit(A: T, i: nat) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
    {
        A[i := false]
    }

    function bitmask_toggle_bit(A: T, i: nat) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
    {
        A[i := !A[i]]
    }


    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Predicates
    ////////////////////////////////////////////////////////////////////////////////


    predicate bitmask_eq(A: T, B: T)
        //  requires Inv(A) && Inv(B)
        ensures bitmask_eq(A, B) <==> A == B
    {
        A == B // just use sequence equality here
    }

    predicate {:opaque} bitmask_is_zeros(A: T)
       //  requires Inv(A)
    {
        forall i | 0 <= i < |A| :: !A[i]
    }

    predicate {:opaque} bitmask_is_ones(A: T)
        // requires Inv(A)
    {
        forall i | 0 <= i < |A| :: A[i]
    }

    lemma lemma_BitmaskZerosPopCnt(A: T)
        requires Inv(A)
        ensures bitmask_is_zeros(A) <==> bitmask_popcnt(A) == 0
    {
        reveal_bitmask_popcnt();
        reveal_bitmask_is_zeros();
    }

    lemma lemma_BitmaskOnesPopCnt(A: T)
        requires Inv(A)
        ensures bitmask_is_ones(A) <==> bitmask_popcnt(A) == bitmask_nbits(A)
    {
        reveal_bitmask_popcnt();
        reveal_bitmask_is_ones();
    }


    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Operations
    ////////////////////////////////////////////////////////////////////////////////


    function {:opaque} bitmask_and(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures forall i | 0 <= i < bitmask_nbits(A) :: bitmask_get_bit(r, i) == (bitmask_get_bit(A, i) && bitmask_get_bit(B, i))
    {
        seq(|A|, i requires 0 <= i < |A| => (A[i] && B[i]))
    }

    function {:opaque}  bitmask_or(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures forall i | 0 <= i < bitmask_nbits(A) :: bitmask_get_bit(r, i) == (bitmask_get_bit(A, i) || bitmask_get_bit(B, i))
    {
        seq(|A|, i requires 0 <= i < |A| => (A[i] || B[i]))
    }

    function {:opaque} bitmask_xor(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures forall i | 0 <= i < bitmask_nbits(A) :: bitmask_get_bit(r, i) == (bitmask_get_bit(A, i) != bitmask_get_bit(B, i))
    {
        seq(|A|, i requires 0 <= i < |A| => (A[i] != B[i]))
    }

    function {:opaque} bitmask_not(A: T) : (r: T)
        // requires Inv(A)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures forall i | 0 <= i < bitmask_nbits(A) :: (bitmask_get_bit(r, i) == !bitmask_get_bit(A, i))
    {
        seq(|A|, i requires 0 <= i < |A| => !A[i])
    }
}
