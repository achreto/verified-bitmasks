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

    //type T = object?

    /// Trait that defines the interface to the Bitmask class
    /// Implementing classes must extend this trait.
    trait BitmaskCode<T> {

        /// the objec type of the bitmask data
        ghost var ghost_data: object;

        var data: T

        /// interpretation functions for the Bitmask Type and the number type
        function I() : (r: S.T)
            reads this
            reads this.ghost_data
            requires Inv()
            ensures S.Inv(r)

        static function ValidSize(n: uint64) : (r : bool)
            ensures r ==> S.ValidSize(n as nat)

        /// invariant, must implie the abstract invariant
        predicate Inv()
            reads this

        ////////////////////////////////////////////////////////////////////////////////
        // Constructor Functions
        ////////////////////////////////////////////////////////////////////////////////

        static method NewZeros(n: uint64) returns (r: BitmaskCode)
            requires ValidSize(n)
            ensures r.Inv()
            ensures fresh(r)
            ensures r.I() == S.bitmask_new_zeros(n as nat)

        static method NewOnes(n: uint64) returns (r: BitmaskCode)
            requires ValidSize(n)
            ensures r.Inv()
            ensures fresh(r)
            ensures r.I() == S.bitmask_new_ones(n as nat)


        ////////////////////////////////////////////////////////////////////////////////
        // Accecssors
        ////////////////////////////////////////////////////////////////////////////////

        // function method get_data() : T
        //     reads this

        ////////////////////////////////////////////////////////////////////////////////
        // Bit Counts
        ////////////////////////////////////////////////////////////////////////////////

        function method nbits() : (r: uint64)
            requires this.Inv()
            reads this
            ensures r as nat == S.bitmask_nbits(this.I())

        method popcnt() returns (r: uint64)
            requires this.Inv()
            ensures r <= this.nbits()
            ensures r as nat == S.bitmask_popcnt(this.I())

        ////////////////////////////////////////////////////////////////////////////////
        // Bitwise Get/Set Operations
        ////////////////////////////////////////////////////////////////////////////////

        method get_bit(i: uint64) returns (r: bool)
            requires this.Inv()
            requires i< this.nbits()
            ensures r == S.bitmask_get_bit(this.I(), i as nat)

        method set_bit(i: uint64)
            requires this.Inv()
            requires i< this.nbits()
            modifies this.ghost_data
            ensures this.Inv()
            ensures this.nbits() == old(this.nbits())
            ensures i < this.nbits()
            ensures this.I() == S.bitmask_set_bit(old(this.I()), i as nat)

        method clear_bit(i: uint64)
            requires this.Inv()
            requires i< this.nbits()
            modifies this.ghost_data
            ensures this.Inv()
            ensures this.nbits() == old(this.nbits())
            ensures this.I() == S.bitmask_clear_bit(old(this.I()), i as nat)

        method toggle_bit(i: uint64)
            requires this.Inv()
            requires i < this.nbits()
            modifies this.ghost_data
            ensures this.Inv()
            ensures this.nbits() == old(this.nbits())
            ensures this.I() == S.bitmask_toggle_bit(old(this.I()), i as nat)

        ////////////////////////////////////////////////////////////////////////////////
        // Bitmask Predicates
        ////////////////////////////////////////////////////////////////////////////////

        method eq(other: BitmaskCode<T>) returns (r: bool)
            requires this.Inv() && other.Inv()
            ensures r <==> S.bitmask_eq(this.I(), other.I())

        method is_zeros() returns (r: bool)
            requires this.Inv()
            ensures r == S.bitmask_is_zeros(this.I())

        method is_ones() returns (r: bool)
            requires this.Inv()
            ensures r == S.bitmask_is_ones(this.I())

        ////////////////////////////////////////////////////////////////////////////////
        // Bitmask Operations
        ////////////////////////////////////////////////////////////////////////////////

        method and(other: BitmaskCode<T>)
            requires this.Inv() && other.Inv()
            requires this.nbits() == other.nbits()
            requires this.ghost_data != other.ghost_data
            modifies this.ghost_data
            ensures this.Inv()
            ensures unchanged(other) && unchanged(other.ghost_data)
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_and(old(this.I()), other.I())

        method or(other: BitmaskCode<T>)
            requires this.Inv() && other.Inv()
            requires this.nbits() == other.nbits()
            requires this.ghost_data != other.ghost_data
            modifies this.ghost_data
            ensures this.Inv()
            ensures unchanged(other) && unchanged(other.ghost_data)
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_or(old(this.I()), other.I())

        method xor(other: BitmaskCode<T>)
            requires this.Inv() && other.Inv()
            requires this.nbits() == other.nbits()
            requires this.ghost_data != other.ghost_data
            modifies this.ghost_data
            ensures this.Inv()
            ensures unchanged(other) && unchanged(other.ghost_data)
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_xor(old(this.I()), other.I())

        method not()
            requires this.Inv()
            modifies this.ghost_data
            ensures this.Inv()
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_not(old(this.I()))
    }
}
