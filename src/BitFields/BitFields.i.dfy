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

include "Spec/BitFields.s.dfy"
include "Spec/MachineTypes.s.dfy"

/// BitFields Module
///
/// This module wraps bitvector operations and provides lemmas for upper-level
/// modules operating on bounded integers to reason about bitwise operations.
///
/// Note: only 64-bit operations are currently supported.
module BitFields {

    import opened MachineTypes
    import opened BitFieldsAxioms

    /// The word size is 64 bits.
    const WORD_SIZE : I := 64

    /// the value representing all ones in the bitvector
    const ALL_ONES : uint64 := 0xffff_ffff_ffff_ffff

    /// represents the integer type (64-bit unsigned integer)
    type I = uint64

    /// represents the bitvector type (64-bit)
    type BV = bv64


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Conversion Function
    ///////////////////////////////////////////////////////////////////////////////////////////////


    function method {:opaque} BitsToWord(b: BV) : I { b as I }
    function method {:opaque} WordToBits(w: I) : BV { w as BV }

    lemma lemma_BitsToWordWordToBits(b: BV)
        ensures WordToBits(BitsToWord(b)) == b
    {
        reveal_BitsToWord(); reveal_WordToBits();
        axiom_as_uint64_as_bv64(b);
    }

    lemma lemma_WordToBitsBitsToWord(a: I)
        ensures BitsToWord(WordToBits(a)) == a
    {
        reveal_BitsToWord(); reveal_WordToBits();
        axiom_as_bv64_as_uint64(a);
    }

    lemma lemma_WordToBitsEq(a: I, b: I)
        requires a == b
        ensures WordToBits(a) == WordToBits(b)
    {
        reveal_BitsToWord(); reveal_WordToBits();
    }

    lemma lemma_BitsToWordEq(a: BV, b: BV)
        requires a == b
        ensures BitsToWord(a) == BitsToWord(b)
    {
        reveal_BitsToWord(); reveal_WordToBits();
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Constructor Functions
    ///////////////////////////////////////////////////////////////////////////////////////////////


    /// constructs a new bitvector where the bit `i` is set
    function method  {:opaque} Bit(i: I) : BV
        requires i < WORD_SIZE
    {
        (1 as BV) << (i as bv7)
    }

    function method {:opaque} BitOnes() : BV {
         0xffff_ffff_ffff_ffff as BV
    }

    function method {:opaque} BitZeros() : BV {
        0x0 as BV
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Bitwise Operations
    ///////////////////////////////////////////////////////////////////////////////////////////////


    /// tests whether the given bit is true
    predicate method {:opaque} BitIsSet(x:BV, i: I)
        requires i < WORD_SIZE
    {
        BitAnd(x, Bit(i)) != 0
    }

    function method {:opaque} BitSetBit(x:BV, i: I) : (r: BV)
        requires i < WORD_SIZE
        ensures BitIsSet(r, i)
    {
        reveal_BitIsSet(); reveal_BitAnd(); reveal_BitOr();
        lemma_BitNotZero(i);

        BitOr(x, Bit(i))
    }

    function method {:opaque} BitClearBit(x:BV, i: I) : (r: BV)
        requires i < WORD_SIZE
        ensures !BitIsSet(r, i)
    {
        reveal_BitIsSet(); reveal_BitAnd(); reveal_Bit(); reveal_BitComp();

        BitAnd(x, BitComp(Bit(i)))
    }

    function method {:opaque} BitToggleBit(x:BV, bit: I) : (r: BV)
        requires bit < WORD_SIZE
        ensures BitIsSet(r, bit) != BitIsSet(x, bit)
    {
        if BitIsSet(x, bit) then BitClearBit(x, bit) else BitSetBit(x, bit)
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Bit Vector Operations
    ///////////////////////////////////////////////////////////////////////////////////////////////


    function method {:opaque} BitAnd(x:BV, y:BV) : (r: BV)
    {
        x & y
    }

    function method {:opaque} BitOr(x:BV, y:BV) : BV
    {
        x | y
    }

    function method {:opaque} BitXor(x:BV, y:BV) : BV
    {
        x ^ y
    }

    function method {:opaque} BitNot(x:BV) : BV
    {
        !x
    }

    function method {:opaque} BitComp(x:BV) : BV
    {
        0xffff_ffff_ffff_ffff ^ x
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Shifts
    ///////////////////////////////////////////////////////////////////////////////////////////////


    function method {:opaque} BitLeftShift(x: BV, i: I) : BV
        requires i < WORD_SIZE
    {
        x << (i as bv7)
    }

    function method {:opaque} BitRightShift(x: BV, i: I) : BV
        requires i < WORD_SIZE
    {
        x >> (i as bv7)
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Arithmetic Operations
    ///////////////////////////////////////////////////////////////////////////////////////////////


    function method {:opaque} BitAdd(x:BV, y:BV) : BV
        /// TODO: handle overflows
    {
        x + y
    }

    function method {:opaque} BitSub(x:BV, y:BV) : BV
        /// TODO: handle underflows
    {
        x - y
    }

    function method {:opaque} BitMod(x:BV, y:BV) : BV
        requires y != 0
    {
        x % y
    }

    function method {:opaque} BitDiv(x:BV, y:BV) : BV
        requires y != 0
    {
        x / y
    }

    function method {:opaque} BitMul(x:BV, y:BV) : BV
        /// TODO: handle overflows
    {
        x * y
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Lemmas and Equalities: AND
    ///////////////////////////////////////////////////////////////////////////////////////////////


    /// idempotent: a & a == a
    lemma lemma_BitAndSelf(a: BV)
        ensures BitAnd(a, a) == a;
    {
        reveal_BitAnd();
    }

    /// Zeroing: a & 0 == 0
    lemma lemma_BitAndZero(a: BV)
        ensures BitAnd(a, 0) == 0;
    {
        reveal_BitAnd();
    }

    /// identity: a & Ones == a
    lemma lemma_BitAndOnes(a: BV)
        ensures BitAnd(a, BitOnes()) == a;
    {
        reveal_BitAnd(); reveal_BitOnes();
    }

    /// commutativity law: a & b == b & a
    lemma lemma_BitAndComm(a: BV, b: BV)
        ensures BitAnd(a, b) == BitAnd(b, a)
    {
        reveal_BitAnd();
    }

    /// associativitly law: a & (b & c) == (a & b) & c
    lemma lemma_BitAndAssoc(a: BV, b: BV, c: BV)
        ensures BitAnd(a, BitAnd(b, c)) == BitAnd(BitAnd(a, b), c)
    {
        reveal_BitAnd();
    }

    /// distribution law: (a & b) & c == (a & c) & (b & c)
    lemma lemma_BitAndDist(a: BV, b: BV, c: BV)
        ensures BitAnd(BitAnd(a, b), c) == BitAnd(BitAnd(a, c), BitAnd(b, c))
    {
        reveal_BitAnd();
    }

    lemma lemma_BitAndCompSelf(a: BV)
        ensures BitAnd(BitComp(a), a) == 0
    {
        reveal_BitAnd(); reveal_BitComp();
    }

    lemma lemma_BitAndNotSelf(a: BV)
        ensures BitAnd(BitNot(a), a) == 0
    {
        reveal_BitAnd(); reveal_BitNot();
    }

    lemma lemma_BitAndBitDist(a: BV, b: BV, i: I)
        requires i < WORD_SIZE
        ensures (BitAnd(BitAnd(a, Bit(i)), BitAnd(b, Bit(i))) == 0)  ==  ((BitAnd(a, Bit(i)) == 0) || (BitAnd(b, Bit(i)) == 0))
    {
        reveal_BitAnd(); reveal_Bit();
    }

    // result is the intersection (a & b)[i] == a[i] && b[i]
    lemma lemma_BitAndIsIntersection(a: BV, b: BV, i: I)
        requires i < WORD_SIZE
        ensures BitIsSet(BitAnd(a, b), i) == (BitIsSet(a, i) && BitIsSet(b, i))
    {
        reveal_BitIsSet();
        if BitIsSet(BitAnd(a, b), i) {
            reveal_BitAnd();
            assert (BitIsSet(a, i) && BitIsSet(b, i));
        } else {
            assert BitAnd(BitAnd(a, Bit(i)), BitAnd(b, Bit(i))) == 0 by {
                lemma_BitAndDist(a, b, Bit(i));
            }
            assert (BitAnd(a, Bit(i)) == 0) || (BitAnd(b, Bit(i)) == 0) by {
                lemma_BitAndBitDist(a, b, i);
            }
            assert !((BitIsSet(a, i) && BitIsSet(b, i)));
        }
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Lemmas and Equalities: OR
    ///////////////////////////////////////////////////////////////////////////////////////////////


     /// idempotent: a | a == a
    lemma lemma_BitOrSelf(a: BV)
        ensures BitOr(a, a) == a;
    {
        reveal_BitOr();
    }

    /// identity: a | 0 == a
    lemma lemma_BitOrZero(a: BV)
        ensures BitOr(a, 0) == a;
    {
        reveal_BitOr();
    }

    /// Ones: a | Ones == Ones
    lemma lemma_BitOrOnes(a: BV)
        ensures BitOr(a, BitOnes()) == BitOnes();
    {
        reveal_BitOr(); reveal_BitOnes();
    }

    /// commutativity law: a | b == b | a
    lemma lemma_BitOrComm(a: BV, b: BV)
        ensures BitOr(a, b) == BitOr(b, a)
    {
        reveal_BitOr();
    }

    /// associativitly law: a | (b | c) == (a | b) | c
    lemma lemma_BitOrAssoc(a: BV, b: BV, c: BV)
        ensures BitOr(a, BitOr(b, c)) == BitOr(BitOr(a, b), c)
    {
        reveal_BitOr();
    }

    /// distribution law: (a | b) | c == (a | c) | (b | c)
    lemma lemma_BitOrDist(a: BV, b: BV, c: BV)
        ensures BitOr(BitOr(a, b), c) == BitOr(BitOr(a, c), BitOr(b, c))
    {
        reveal_BitOr();
    }

    /// (a | b) == 0 ===> a == 0 && b == 0
    lemma lemma_BitOrZeroImpliesArgs(a: BV, b:BV)
        requires BitOr(a, b) == 0
        ensures a == 0 && b == 0
    {
        reveal_BitOr();
    }

    /// The result of Or-ing two numbers together
    lemma lemma_BitOrIsUnion(a: BV, b: BV, i: I)
        requires i < WORD_SIZE
        ensures BitIsSet(BitOr(a, b), i) == (BitIsSet(a, i) || BitIsSet(b, i))
    {
        reveal_BitIsSet();
        calc {
            BitAnd(BitOr(a, b), Bit(i));
            { lemma_BitAndOrDist(a, b, Bit(i)); }
            BitOr(BitAnd(a, Bit(i)), BitAnd(b, Bit(i)));
        }

        if !BitIsSet(BitOr(a, b), i) {
            lemma_BitOrZeroImpliesArgs(BitAnd(a, Bit(i)), BitAnd(b, Bit(i)));
        } else {
            reveal_BitOr();
        }
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Lemmas and Equalities: XOR
    ///////////////////////////////////////////////////////////////////////////////////////////////


     /// Clearing with Self: a ^ a == 0
    lemma lemma_BitXorSelf(a: BV)
        ensures BitXor(a, a) == 0;
    {
        reveal_BitXor();
    }

    /// identity: a ^ 0 == a
    lemma lemma_BitXorZero(a: BV)
        ensures BitXor(a, 0) == a;
    {
        reveal_BitXor();
    }

    /// Ones: a ^ Ones == a
    lemma lemma_BitXorOnes(a: BV)
        ensures BitXor(a, BitOnes()) == BitNot(a);
    {
        reveal_BitXor(); reveal_BitOnes(); reveal_BitNot();
    }

    /// commutativity law: a ^ b == b ^ a
    lemma lemma_BitXorComm(a: BV, b: BV)
        ensures BitXor(a, b) == BitXor(b, a)
    {
        reveal_BitXor();
    }

    /// associativitly law: a ^ (b ^ c) == (a ^ b) ^ c
    lemma lemma_BitXorAssoc(a: BV, b: BV, c: BV)
        ensures BitXor(a, BitXor(b, c)) == BitXor(BitXor(a, b), c)
    {
        reveal_BitXor();
    }

    /// (a ^ b) == 0 ===> a == b
    lemma lemma_BitXorZeroImpliesArgs(a: BV, b:BV)
        requires BitXor(a, b) == 0
        ensures a == b
    {
        reveal_BitXor();
    }

    /// Xor is the two not equal: (a ^ b)[i] == (a[i] != b[i])
    lemma lemma_BitXorIsNotEq(a: BV, b: BV, i: I)
        requires i < WORD_SIZE
        ensures BitIsSet(BitXor(a, b), i) == (BitIsSet(a, i) != BitIsSet(b, i))
    {
        reveal_BitIsSet(); reveal_BitAnd(); reveal_Bit(); reveal_BitXor();
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Lemmas and Equalities: Not and Comp
    ///////////////////////////////////////////////////////////////////////////////////////////////


    lemma lemma_BitNotNot(a: BV)
        ensures BitNot(BitNot(a)) == a;
    {
        reveal_BitNot();
    }

    lemma lemma_BitCompComp(a: BV)
        ensures BitComp(BitComp(a)) == a;
    {
        reveal_BitComp();
    }

    lemma BitNotCompEq(a: BV)
        ensures BitNot(a) == BitComp(a);
    {
        reveal_BitNot(); reveal_BitComp();
    }

    lemma lemma_BitNotIsNot(a: BV, i: I)
        requires i < WORD_SIZE
        ensures BitIsSet(BitNot(a), i) == !BitIsSet(a, i)
    {
        reveal_BitIsSet(); reveal_BitNot(); reveal_BitAnd(); reveal_Bit();
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Shifts
    ///////////////////////////////////////////////////////////////////////////////////////////////

    // TODO


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Constructors
    ///////////////////////////////////////////////////////////////////////////////////////////////


    lemma lemma_BitNotZero(i: I)
        requires i < WORD_SIZE
        ensures Bit(i) != 0
    {
        reveal_Bit();
    }

    lemma lemma_BitBitIsSet(i: I)
        requires i < WORD_SIZE
        ensures BitIsSet(Bit(i), i)
    {
        reveal_Bit(); reveal_BitIsSet(); reveal_BitAnd();
    }

    lemma lemma_BitNotSetBits(i: I, j: I)
        requires i < WORD_SIZE
        requires j < WORD_SIZE
        requires i != j
        ensures !BitIsSet(Bit(i), j)
    {
        reveal_Bit(); reveal_BitIsSet(); reveal_BitAnd();
    }

    // two bits are not equal
    lemma lemma_BitNotEqualAndZero(i: I, j: I)
        requires i != j
        requires i < WORD_SIZE
        requires j < WORD_SIZE
        ensures BitAnd(Bit(i), Bit(j)) == 0
    {
        reveal_Bit(); reveal_BitAnd();
    }

    lemma lemma_BitOnesBitIsSet(i: I)
        requires i < WORD_SIZE
        ensures BitIsSet(BitOnes(), i)
    {
        reveal_BitIsSet(); reveal_BitAnd(); reveal_BitOnes(); reveal_Bit();
        lemma_BitAndOnes(Bit(i));
    }

    lemma lemma_BitZerosNotBitIsSet(i: I)
        requires i < WORD_SIZE
        ensures !BitIsSet(BitZeros(), i)
    {
        reveal_BitIsSet(); reveal_BitAnd(); reveal_BitZeros(); reveal_Bit();
        lemma_BitAndZero(Bit(i));
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Setting Individual Bits
    ///////////////////////////////////////////////////////////////////////////////////////////////


    lemma lemma_BitSetSelf(a: BV, i: I)
        requires i < WORD_SIZE
        ensures BitIsSet(BitSetBit(a, i), i)
    {
    }

    lemma lemma_BitSetOther(a: BV, i: I, j: I)
        requires i < 64
        requires j < 64
        requires i != j
        ensures BitIsSet(a, j) <==> BitIsSet(BitSetBit(a, i), j)
    {
        reveal_BitIsSet(); reveal_BitSetBit();
        lemma_BitAndOrDist(a, Bit(i), Bit(j));
        lemma_BitNotEqualAndZero(i, j);
        lemma_BitOrZero(BitAnd(a, Bit(j)));
    }

    lemma lemma_BitClearSelf(a: BV, i: I)
        requires i < WORD_SIZE
        ensures !BitIsSet(BitClearBit(a, i), i)
    {
    }

    lemma lemma_BitClearOther(a: BV, i: I, j: I)
        requires i < 64
        requires j < 64
        requires i != j
        ensures BitIsSet(a, j) <==> BitIsSet(BitClearBit(a, i), j)
    {
        reveal_BitIsSet(); reveal_BitClearBit();
        lemma_BitAndAssoc(a, BitComp(Bit(i)), Bit(j));
        lemma_BitCompNotEqual(i, j);
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Distribution of And/Or
    ///////////////////////////////////////////////////////////////////////////////////////////////

    lemma lemma_BitAndOrDist(a: BV, b: BV, c: BV)
        ensures BitAnd(BitOr(a, b), c) == BitOr(BitAnd(a, c), BitAnd(b, c))
    {
        reveal_BitAnd(); reveal_BitOr();
    }

    lemma lemma_BitOrAndDist(a: BV, b: BV, c: BV)
        ensures BitOr(BitAnd(a, b), c) == BitAnd(BitOr(a, c), BitOr(b, c))
    {
        reveal_BitAnd(); reveal_BitOr();
    }

    lemma lemma_BitOrAndSelf(a: BV, b: BV)
        ensures BitAnd(BitOr(a, b), b) == b
    {
        reveal_BitAnd(); reveal_BitOr();
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // DeMorgan's Laws
    ///////////////////////////////////////////////////////////////////////////////////////////////

    lemma lemma_BitDeMorgan(a: BV, b: BV)
        ensures BitNot(BitOr(a, b)) == BitAnd(BitNot(a), BitNot(b))
    {
        reveal_BitAnd(); reveal_BitNot(); reveal_BitOr();
    }

    lemma lemma_BitDeMorgan2(a: BV, b: BV)
        ensures BitNot(BitAnd(a, b)) == BitOr(BitNot(a), BitNot(b))
    {
        reveal_BitAnd(); reveal_BitNot(); reveal_BitOr();
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Others
    ///////////////////////////////////////////////////////////////////////////////////////////////


    lemma lemma_BitCompNotEqual(i: I, j: I)
        requires i != j
        requires i < 64
        requires j < 64
        ensures BitAnd(BitComp(Bit(i)), Bit(j)) == Bit(j)
    {
        reveal_Bit(); reveal_BitAnd(); reveal_BitAnd(); reveal_BitComp();
    }
}
