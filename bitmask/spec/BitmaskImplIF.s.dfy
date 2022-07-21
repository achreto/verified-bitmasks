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
    /// declares the type for numbers
    type R(==)

    /// interpretation functions for the Bitmask Type and the number type
    function IT(A: T) : (r: S.T)
        requires Inv(A)
        ensures S.Inv(r)

    function IR(r: R) : S.R

    /// invariant, must implie the abstract invariant
    predicate Inv(A: T)

    /// whether or not the size parameter is valid
    predicate ValidSize(n: R)
        ensures  ValidSize(n) ==> S.ValidSize(IR(n))

    /// converts the type R to a nat
    function ToNat(n: R) : nat
        ensures ToNat(n) == S.ToNat(IR(n))

    function ToBitSeq(A: T) : seq<bool>

    ////////////////////////////////////////////////////////////////////////////////
    // Constructor Functions
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_new_zeros(M: R) : (r: T)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_zeros(r)
        ensures IT(r) == S.bitmask_new_zeros(IR(M))

    function bitmask_new_ones(M: R) : (r: T)
        ensures Inv(r)
        ensures M == bitmask_nbits(r)
        ensures bitmask_is_ones(r)
        ensures IT(r) == S.bitmask_new_ones(IR(M))

    ////////////////////////////////////////////////////////////////////////////////
    // Bit Counts
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_nbits(A: T) : (r: R)
        // requires Inv(A)
        ensures IR(r) == S.bitmask_nbits(IT(A))

    function bitmask_popcnt(A: T) : (r: R)
        //requires Inv(A)
        ensures ToNat(r) <= ToNat(bitmask_nbits(A))
        ensures IR(r) == S.bitmask_popcnt(IT(A))

    ////////////////////////////////////////////////////////////////////////////////
    // Bitwise Get/Set Operations
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_get_bit(A: T, i: R) : (r: bool)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures r == S.bitmask_get_bit(IT(A), IR(i));

    function bitmask_set_bit(A: T, i: R) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures IT(r) == S.bitmask_set_bit(IT(A), IR(i));

    function bitmask_clear_bit(A: T, i: R) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures IT(r) == S.bitmask_clear_bit(IT(A), IR(i));

    function bitmask_toggle_bit(A: T, i: R) : (r: T)
        // requires Inv(A)
        // requires ToNat(i) < ToNat(bitmask_nbits(A))
        ensures IT(r) == S.bitmask_toggle_bit(IT(A), IR(i));

    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Predicates
    ////////////////////////////////////////////////////////////////////////////////

    predicate bitmask_eq(A: T, B: T)
        // requires Inv(A) && Inv(B)
        ensures bitmask_eq(A, B) <==> A == B
        ensures bitmask_eq(A, B) <==> S.bitmask_eq(IT(A), IT(B))

    predicate bitmask_is_zeros(A: T)
        // requires Inv(A)
        ensures bitmask_is_zeros(A) <==> S.bitmask_is_zeros(IT(A))

    predicate bitmask_is_ones(A: T)
        // requires Inv(A)
        ensures bitmask_is_ones(A) <==> S.bitmask_is_ones(IT(A))

    ////////////////////////////////////////////////////////////////////////////////
    // Bitmask Operations
    ////////////////////////////////////////////////////////////////////////////////

    function bitmask_and(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures IT(r) == S.bitmask_and(IT(A), IT(B))

    function bitmask_or(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures IT(r) == S.bitmask_or(IT(A), IT(B))

    function bitmask_xor(A: T, B: T) : (r: T)
        // requires Inv(A) && Inv(B)
        // requires bitmask_nbits(A) == bitmask_nbits(B)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures IT(r) == S.bitmask_xor(IT(A), IT(B))

    function bitmask_not(A: T) : (r: T)
        // requires Inv(A)
        ensures Inv(r)
        ensures bitmask_nbits(r) == bitmask_nbits(A)
        ensures IT(r) == S.bitmask_not(IT(A))
}