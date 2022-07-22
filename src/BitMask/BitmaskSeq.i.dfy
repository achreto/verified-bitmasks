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
include "Spec/BitmaskCodeIF.s.dfy"


/// Executable Implementation of a BitMask with an array of booleans
module BitmaskSeq refines BitmaskCodeIF {

    /// get the bitmask specification module
    import S = BitmaskSpec

    class BitmaskArray //extends BitmaskCode<array<bool>>
    {
        ghost var len : nat
        var data: seq<bool>

        function I() : (r: S.T)
            requires Inv()
            reads this
            ensures S.Inv(r)
        {
            this.data[..]
        }

        // static function ValidSize(n: uint64) : (r : bool)
        //     ensures r ==> S.ValidSize(n as nat)
        // {
        //     true
        // }

        predicate Inv()
            reads this
        {
            && |this.data| <= UINT64_MAX()
            && |this.data| == this.len
        }

        ////////////////////////////////////////////////////////////////////////////////
        // Constructor Functions
        ////////////////////////////////////////////////////////////////////////////////

        constructor CNewZeros(n: uint64)
            ensures this.Inv()
            ensures fresh(this)
            ensures this.I() == S.bitmask_new_zeros(n as nat)
        {
            this.len := n as nat;
            this.data := seq(n, i => false);
            S.reveal_bitmask_new_zeros();
        }

        constructor CNewOnes(n: uint64)
            ensures this.Inv()
            ensures fresh(this)
            ensures this.I() == S.bitmask_new_ones(n as nat)
        {
            this.len := n as nat;
            this.data := seq(n, i => true);
            S.reveal_bitmask_new_ones();
        }

        ////////////////////////////////////////////////////////////////////////////////
        // Bit Counts
        ////////////////////////////////////////////////////////////////////////////////

        function method nbits() : (r: uint64)
            requires this.Inv()
            reads this
            ensures r as nat == S.bitmask_nbits(this.I())
        {
            |this.data| as uint64
        }

        method popcnt() returns (r: uint64)
            requires this.Inv()
            ensures r <= this.nbits()
            ensures r as nat == S.bitmask_popcnt(this.I())
        {
            var len := this.nbits();

            var bits : uint64 := 0;
            var i := 0;
            S.reveal_bitmask_popcnt();
            while i < len
            invariant 0 <= i <= len;
            invariant bits <= i;
            invariant bits as nat == S.bitmask_popcnt(this.I()[..i])
            {
                assert this.I()[..i+1] == this.I()[..i] + [this.I()[i]];
                assert S.bitmask_popcnt(this.I()[..i+1]) == S.bitmask_popcnt(this.I()[..i]) + S.bitmask_popcnt(this.I()[i..i+1]) by {
                    S.PopcntDist(this.I()[..i], this.I()[i..i+1]);
                }

                if this.data[i] {
                    bits := bits + 1;
                    assert S.bitmask_popcnt(this.I()[i..i+1]) == 1;
                } else {
                    assert S.bitmask_popcnt(this.I()[i..i+1]) == 0;
                }
                i := i + 1;
            }
            assert this.I()[..i] == this.I();
            assert bits as nat == S.bitmask_popcnt(this.I()[..i]);
            r := bits;
        }

        ////////////////////////////////////////////////////////////////////////////////
        // Bitwise Get/Set Operations
        ////////////////////////////////////////////////////////////////////////////////

        method get_bit(i: uint64) returns (r: bool)
            requires this.Inv()
            requires i< this.nbits()
            ensures r == S.bitmask_get_bit(this.I(), i as nat)
        {
            return this.data[i];
        }

        method set_bit(i: uint64)
            requires this.Inv()
            requires i< this.nbits()
            modifies this
            ensures this.Inv()
            ensures this.nbits() == old(this.nbits())
            ensures i < this.nbits()
            ensures this.I() == S.bitmask_set_bit(old(this.I()), i as nat)
        {
            this.data := this.data[i := true];
        }

        method clear_bit(i: uint64)
            requires this.Inv()
            requires i< this.nbits()
            modifies this
            ensures this.Inv()
            ensures this.nbits() == old(this.nbits())
            ensures this.I() == S.bitmask_clear_bit(old(this.I()), i as nat)
        {
            this.data := this.data[i := false];
        }

        method toggle_bit(i: uint64)
            requires this.Inv()
            requires i < this.nbits()
            modifies this
            ensures this.Inv()
            ensures this.nbits() == old(this.nbits())
            ensures this.I() == S.bitmask_toggle_bit(old(this.I()), i as nat)
        {
            this.data := this.data[i := !this.data[i]];
        }

        ////////////////////////////////////////////////////////////////////////////////
        // Bitmask Predicates
        ////////////////////////////////////////////////////////////////////////////////

        method eq(other: BitmaskArray) returns (r: bool)
            requires this.Inv() && other.Inv()
            ensures r <==> S.bitmask_eq(this.I(), other.I())
        {
            var len := this.nbits();
            if len != other.nbits() {
                return false;
            }

            var i := 0;
            while i < len
            invariant 0 <= i <= len;
            invariant forall j :: 0 <= j < i ==> this.data[j] == other.data[j];
            {
                if (this.data[i] != other.data[i]) {
                    r := false;
                    return;
                }
                i := i + 1;
            }
            r := true;
        }

        method is_zeros() returns (r: bool)
            requires this.Inv()
            ensures r == S.bitmask_is_zeros(this.I())
        {
            r := true;
            var len := this.nbits();
            var i := 0;

            S.reveal_bitmask_is_zeros();
            while i < len
                invariant 0 <= i <= len;
                invariant forall j | 0 <= j < i :: !this.data[j]
            {
                if this.data[i] {
                    r := false;
                    return;
                }
                i := i + 1;
            }
        }

        method is_ones() returns (r: bool)
            requires this.Inv()
            ensures r == S.bitmask_is_ones(this.I())
        {
            r := true;
            var len := this.nbits();
            var i := 0;
            S.reveal_bitmask_is_ones();
            while i < len
                invariant 0 <= i <= len;
                invariant forall j | 0 <= j < i :: this.data[j]
            {
                if !this.data[i] {
                    r := false;
                    return;
                }
                i := i + 1;
            }
        }

        ////////////////////////////////////////////////////////////////////////////////
        // Bitmask Operations
        ////////////////////////////////////////////////////////////////////////////////

        method and(other:BitmaskArray)
            requires this.Inv() && other.Inv()
            requires this.nbits() == other.nbits()
            requires this != other
            modifies this
            ensures this.Inv()
            ensures unchanged(other)
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_and(old(this.I()), other.I())
        {
            S.reveal_bitmask_and();
            this.data := seq(|this.data|, i requires 0 <= i < |this.data| &&  |this.data| == |other.data| reads this reads other =>  (this.data[i] && other.data[i]));
        }


        method or(other:BitmaskArray)
            requires this.Inv() && other.Inv()
            requires this.nbits() == other.nbits()
            requires this != other
            modifies this
            ensures this.Inv()
            ensures unchanged(other)
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_or(old(this.I()), other.I())
        {
            S.reveal_bitmask_or();
            assert |this.data|  == |other.data|;
            this.data := seq(|this.data|, i requires 0 <= i < |this.data| &&  |this.data| == |other.data| reads this reads other =>  (this.data[i] || other.data[i]));
        }

        method xor(other:BitmaskArray)
            requires this.Inv() && other.Inv()
            requires this.nbits() == other.nbits()
            requires this != other
            modifies this
            ensures this.Inv()
            ensures unchanged(other)
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_xor(old(this.I()), other.I())
        {
            S.reveal_bitmask_xor();
            assert |this.data|  == |other.data|;
            this.data := seq(|this.data|, i requires 0 <= i < |this.data| &&  |this.data| == |other.data| reads this reads other =>  (this.data[i] != other.data[i]));
        }

        method not()
            requires this.Inv()
            modifies this
            ensures this.Inv()
            ensures this.nbits() == old(this).nbits()
            ensures this.I() == S.bitmask_not(old(this.I()))
        {
            S.reveal_bitmask_not();
            this.data := seq(|this.data|, i requires 0 <= i < |this.data| reads this =>  !this.data[i]);
        }
    }
}

