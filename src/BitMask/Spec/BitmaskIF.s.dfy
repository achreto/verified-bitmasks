
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

/// Bitmask Interface Moddule
///
/// This abstract module provides the interface to manipulate bitmasks.
/// Other bitmask implementation modules should ultimately refine this
/// abstract module. However, this refinement should not be done directly
/// other than in the BitmaskSpec module. Any other module should refine
/// BitmaskImplIF (that in turn refines BitmaskIF).
abstract module BitmaskIF {


    ////////////////////////////////////////////////////////////////////////////////
    // Types Definitions
    ////////////////////////////////////////////////////////////////////////////////

    /// declares the type for the bitmask
    type T

    /// Invariant over the bitmask type T
    predicate Inv(A: T)

    /// predicate whether the size `n` is supported by the bitmask type T
    predicate ValidSize(n: nat)

    /// Predicate whether the bit `i` is valid for the bitmask `A`
    predicate ValidBit(A: T, i: nat)

    /// converts the bitmask type to a sequence of booleans
    function ToBitSeq(A: T) : seq<bool>

    ////////////////////////////////////////////////////////////////////////////////
    // Constructor Functions
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_new_zeros(M: nat) : (r: T)
        requires ValidSize(M)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_zeros(r)

    function bitmask_new_ones(M: nat) : (r: T)
        requires ValidSize(M)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_ones(r)

    // some concatenation function
    function bitmask_concat(A: T, B: T) : (r: T)
        requires Inv(A) && Inv(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A) + bitmask_nbits(B)
        ensures ToBitSeq(r) == ToBitSeq(A) + ToBitSeq(B)

    function bitmask_split(A: T, i: nat) : (r:(T, T))
        requires Inv(A)
        requires i <= bitmask_nbits(A)
        ensures Inv(r.0) && Inv(r.1 )
        ensures ToBitSeq(A) == ToBitSeq(r.0) + ToBitSeq(r.1)

    lemma lemma_bitmask_split_concat(A: T, B: T, i: nat)
        requires Inv(A) && Inv(B)
        ensures A == bitmask_split(bitmask_concat(A, B), bitmask_nbits(A)).0
        ensures B == bitmask_split(bitmask_concat(A, B), bitmask_nbits(A)).1


    ////////////////////////////////////////////////////////////////////////////////
    // Size
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_nbits(A: T) : (r: nat)
        requires Inv(A)

    function bitmask_popcnt(A: T) : (r: nat)
        requires Inv(A)
        ensures r <= bitmask_nbits(A)


    ////////////////////////////////////////////////////////////////////////////////
    // Bitwise Get/Set Operations
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_get_bit(A: T, i: nat) : (r: bool)
        requires Inv(A)
        requires i < bitmask_nbits(A)

    function bitmask_set_bit(A: T, i: nat) : (r: T)
        requires Inv(A)
        requires i < bitmask_nbits(A)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures bitmask_get_bit(r, i)

    function bitmask_clear_bit(A: T, i: nat) : (r: T)
        requires Inv(A)
        requires i < bitmask_nbits(A)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures !bitmask_get_bit(r, i)

    function bitmask_toggle_bit(A: T, i: nat) : (r: T)
        requires Inv(A)
        requires i < bitmask_nbits(A)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures bitmask_get_bit(r, i) == !bitmask_get_bit(A, i)


    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Predicates
    ////////////////////////////////////////////////////////////////////////////////


    predicate bitmask_eq(A: T, B: T)
        requires Inv(A) && Inv(B)
        ensures bitmask_eq(A, B) <==> A == B

    predicate bitmask_is_zeros(A: T)
        requires Inv(A)

    predicate bitmask_is_ones(A: T)
        requires Inv(A)


    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Operations
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_and(A: T, B: T) : (r: T)
        requires Inv(A) && Inv(B)
        requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)

    function bitmask_or(A: T, B: T) : (r: T)
        requires Inv(A) && Inv(B)
        requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)

    function bitmask_xor(A: T, B: T) : (r: T)
        requires Inv(A) && Inv(B)
        requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)

    function bitmask_not(A: T) : (r: T)
        requires Inv(A)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
}
