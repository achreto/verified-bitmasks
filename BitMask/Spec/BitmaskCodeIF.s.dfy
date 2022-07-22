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

include "../../BitFields/Spec/MachineTypes.s.dfy"
include "BitmaskImplIF.s.dfy"

/// Abstract representing implementing code
///
/// Any module that has executable code must refine from this module.
abstract module BitmaskCodeIF {

    import opened MachineTypes

    // The implementation specification of the bitmask
    import S : BitmaskImplIF

    /// Trait that defines the interface to the Bitmask class
    /// Implementing classes must extend this trait.
    trait BitmaskCode {
        /// interpretation functions for the Bitmask Type and the number type
        function I() : (r: S.T)
            reads this
            requires Inv()
            ensures S.Inv(r)

        function IR(r: uint64) : S.R

        /// invariant, must implie the abstract invariant
        predicate Inv()


        /// converts the type R to a nat
        function ToNat(n: uint64) : nat
            ensures ToNat(n) == S.ToNat(IR(n))

        ////////////////////////////////////////////////////////////////////////////////
        // Constructor Functions
        ////////////////////////////////////////////////////////////////////////////////

        // method bitmask_new_zeros(N: uint64) returns (r: BitmaskCode)
        //     ensures r.Inv()

        // method bitmask_new_ones(N: uint64) returns (r: BitmaskCode)


        ////////////////////////////////////////////////////////////////////////////////
        // Bit Counts
        ////////////////////////////////////////////////////////////////////////////////

        function method nbits() : (r: uint64)
            requires this.Inv()
            ensures IR(r) == S.bitmask_nbits(this.I())

        method popcnt() returns (r: uint64)
            requires this.Inv()
            ensures ToNat(r) <= ToNat(this.nbits())
            ensures IR(r) == S.bitmask_popcnt(this.I())

        ////////////////////////////////////////////////////////////////////////////////
        // Bitwise Get/Set Operations
        ////////////////////////////////////////////////////////////////////////////////

        method get_bit(i: uint64) returns (r: bool)
            requires this.Inv()
            requires ToNat(i) < ToNat(this.nbits())
            ensures r == S.bitmask_get_bit(this.I(), IR(i))

        method set_bit(i: uint64)
            requires this.Inv()
            requires ToNat(i) < ToNat(this.nbits())
            modifies this
            ensures this.Inv()
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_set_bit(old(this).I(), IR(i))

        method clear_bit(i: uint64)
            requires this.Inv()
            requires ToNat(i) < ToNat(this.nbits())
            modifies this
            ensures this.Inv()
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_clear_bit(old(this).I(), IR(i))

        method toggle_bit(i: uint64)
            requires this.Inv()
            requires ToNat(i) < ToNat(this.nbits())
            modifies this
            ensures this.Inv()
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_toggle_bit(old(this).I(), IR(i))

        ////////////////////////////////////////////////////////////////////////////////
        // Bitmask Predicates
        ////////////////////////////////////////////////////////////////////////////////

        predicate method eq(other: BitmaskCode)
            requires this.Inv() && other.Inv()
            ensures this.eq(other) <==> S.bitmask_eq(this.I(), other.I())

        predicate method is_zeros()
            requires this.Inv()
            ensures this.is_zeros() <==> S.bitmask_is_zeros(this.I())

        predicate method is_ones()
            requires this.Inv()
            ensures this.is_ones() <==> S.bitmask_is_ones(this.I())

        ////////////////////////////////////////////////////////////////////////////////
        // Bitmask Operations
        ////////////////////////////////////////////////////////////////////////////////

        method and(other: BitmaskCode)
            requires this.Inv() && other.Inv()
            requires this.nbits() == other.nbits()
            ensures this.Inv()
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_not(old(this).I())

        method or(other: BitmaskCode)
            requires this.Inv() && other.Inv()
            requires this.nbits() == other.nbits()
            ensures this.Inv()
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_not(old(this).I())


        method xor(other: BitmaskCode)
            requires this.Inv() && other.Inv()
            requires this.nbits() == other.nbits()
            ensures this.Inv()
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_not(old(this).I())

        method not()
            requires this.Inv()
            ensures this.Inv()
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_not(old(this).I())
    }
}
