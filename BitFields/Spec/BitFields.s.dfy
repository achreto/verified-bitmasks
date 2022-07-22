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


/// BitField Axioms Module
///
/// This module contains axioms to reason about BitFields represented at
/// bitvectors in Dafny. The axioms ensure that converting a bounded integer
/// to a bitvector and back results in the original value (and vice versa).
module BitFieldsAxioms {

    import opened MachineTypes

    lemma {:axiom} axiom_as_uint64_as_bv64(a: bv64)
        ensures (a as uint64) as bv64 == a

    lemma {:axiom} axiom_as_bv64_as_uint64(a: uint64)
        ensures (a as bv64) as uint64 == a

    lemma {:axiom} axiom_as_uint32_as_bv32(a: bv32)
            ensures (a as uint32) as bv32 == a

    lemma {:axiom} axiom_as_bv32_as_uint32(a: uint32)
        ensures (a as bv32) as uint32 == a

    lemma {:axiom} axiom_as_uint16_as_bv16(a: bv16)
            ensures (a as uint16) as bv16 == a

    lemma {:axiom} axiom_as_bv16_as_uint16(a: uint16)
        ensures (a as bv16) as uint16 == a

    lemma {:axiom} axiom_as_uint8_as_bv8(a: bv8)
            ensures (a as uint8) as bv8 == a

    lemma {:axiom} axiom_as_bv8_as_uint8(a: uint8)
        ensures (a as bv8) as uint8 == a
}
