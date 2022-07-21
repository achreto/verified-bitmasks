
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

include "MachineTypes.s.dfy"

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

    /// declares the type for numbers
    /// TODO: should we just get rid of this and use `nat` instead?
    type R(==, !new)

    /// converts the type R to a nat
    function ToNat(n: R) : nat
    function FromNat(n: nat) : R

    /// Invariant over the bitmask type T
    predicate Inv(A: T)

    /// predicate whether the size `n` is supported by the bitmask type T
    predicate ValidSize(n: R)

    /// Predicate whether the bit `i` is valid for the bitmask `A`
    predicate ValidBit(A: T, i: R)


    ////////////////////////////////////////////////////////////////////////////////
    // Constructor Functions
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_new_zeros(M: R) : (r: T)
        requires ValidSize(M)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_zeros(r)

    function bitmask_new_ones(M: R) : (r: T)
        requires ValidSize(M)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_ones(r)

    // some concatenation function
    function bitmask_concat(A: T, B: T) : (r: T)
        //ensures bitmask_nbits(r) == bitmask_nbits(A) + bitmask_nbits(B)
        // ensures the bits are concatenated
        // ensures A == bitmask_split(r, bitmask_nbits(A)).0
        // ensures B == bitmask_split(r, bitmask_nbits(A)).1

    function bitmask_split(A: T, i: R) : (r:(T, T))
        ensures bitmask_concat(r.0, r.1) == A

    lemma lemma_bitmask_split_concat(A: T, B: T)
        requires Inv(A) && Inv(B)
        ensures A == bitmask_split(bitmask_concat(A, B), bitmask_nbits(A)).0
        ensures B == bitmask_split(bitmask_concat(A, B), bitmask_nbits(A)).1


    ////////////////////////////////////////////////////////////////////////////////
    // Size
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_nbits(A: T) : (r: R)
        requires Inv(A)

    function bitmask_popcnt(A: T) : (r: R)
        requires Inv(A)
        ensures ToNat(r) <= ToNat(bitmask_nbits(A))


    ////////////////////////////////////////////////////////////////////////////////
    // Bitwise Get/Set Operations
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_get_bit(A: T, i: R) : (r: bool)
        requires Inv(A)
        requires ToNat(i) < ToNat(bitmask_nbits(A))

    function bitmask_set_bit(A: T, i: R) : (r: T)
        requires Inv(A)
        requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures bitmask_get_bit(r, i)

    function bitmask_clear_bit(A: T, i: R) : (r: T)
        requires Inv(A)
        requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures !bitmask_get_bit(r, i)

    function bitmask_toggle_bit(A: T, i: R) : (r: T)
        requires Inv(A)
        requires ToNat(i) < ToNat(bitmask_nbits(A))
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
