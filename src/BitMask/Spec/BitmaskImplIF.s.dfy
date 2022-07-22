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


/// Abstract module for the other implementing bitmask modules
///
/// All modules other than `BitmaskSpec` should refine this module.
/// The module defines the interfaces as well as refinement structure
/// of the bitmask implemention.
abstract module BitmaskImplIF refines BitmaskIF {

    ////////////////////////////////////////////////////////////////////////////////
    // Types Definitions
    ////////////////////////////////////////////////////////////////////////////////

    /// The specification of the bitmask. This is the higher-level module
    /// that this module refines.
    import S : BitmaskIF

    /// declares the type for the bitmask
    type T

    /// interpretation functions for the Bitmask Type and the number type
    function I(A: T) : (r: S.T)
        requires Inv(A)
        ensures S.Inv(r)

    /// invariant, must implie the abstract invariant
    predicate Inv(A: T)

    /// whether or not the size parameter is valid
    predicate ValidSize(n: nat)
        ensures  ValidSize(n) ==> S.ValidSize(n)


    ////////////////////////////////////////////////////////////////////////////////
    // Constructor Functions
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_new_zeros(M: nat) : (r: T)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_zeros(r)
        ensures I(r) == S.bitmask_new_zeros(M)

    function bitmask_new_ones(M: nat) : (r: T)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_ones(r)
        ensures I(r) == S.bitmask_new_ones(M)

    ////////////////////////////////////////////////////////////////////////////////
    // Bit Counts
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_nbits(A: T) : (r: nat)
        // requires Inv(A)
        ensures r == S.bitmask_nbits(I(A))

    function bitmask_popcnt(A: T) : (r: nat)
        //requires Inv(A)
        ensures r <= bitmask_nbits(A)
        ensures r == S.bitmask_popcnt(I(A))


    ////////////////////////////////////////////////////////////////////////////////
    // Bitwise Get/Set Operations
    ////////////////////////////////////////////////////////////////////////////////


    function bitmask_get_bit(A: T, i: nat) : (r: bool)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures r == S.bitmask_get_bit(I(A), i);

    function bitmask_set_bit(A: T, i: nat) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures I(r) == S.bitmask_set_bit(I(A), i);

    function bitmask_clear_bit(A: T, i: nat) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures I(r) == S.bitmask_clear_bit(I(A), i);

    function bitmask_toggle_bit(A: T, i: nat) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures I(r) == S.bitmask_toggle_bit(I(A), i);


    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Predicates
    ////////////////////////////////////////////////////////////////////////////////


    predicate bitmask_eq(A: T, B: T)
        // requires Inv(A) && Inv(B)
        ensures bitmask_eq(A, B) <==> A == B
        ensures bitmask_eq(A, B) <==> S.bitmask_eq(I(A), I(B))

    predicate bitmask_is_zeros(A: T)
        // requires Inv(A)
        ensures bitmask_is_zeros(A) <==> S.bitmask_is_zeros(I(A))

    predicate bitmask_is_ones(A: T)
        // requires Inv(A)
        ensures bitmask_is_ones(A) <==> S.bitmask_is_ones(I(A))

    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Operations
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_and(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures I(r) == S.bitmask_and(I(A), I(B))

    function bitmask_or(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures I(r) == S.bitmask_or(I(A), I(B))

    function bitmask_xor(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures I(r) == S.bitmask_xor(I(A), I(B))

    function bitmask_not(A: T) : (r: T)
        // requires Inv(A)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures I(r) == S.bitmask_not(I(A))
}