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
    // Helper Functions
    ///////////////////////////////////////////////////////////////////////////////////////////////

    /// a predicate for the inrange condition of the bits
    /// intended to be used in foralls.
    predicate InRange(i: I, n: I) {
        0 <= i && i < n
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // From/To Seq<bool>
    ///////////////////////////////////////////////////////////////////////////////////////////////

    function {:opaque} BitsToSeqBool(b: BV) : (r: seq<bool>)
        ensures |r| == WORD_SIZE as nat
        ensures forall i | InRange(i, WORD_SIZE) :: r[i] == BitIsSet(b, i)
    {
        seq(WORD_SIZE, i requires 0 <= i < WORD_SIZE as nat => BitIsSet(b, i as I))
    }

    function {:opaque} SeqBoolToBitsHelper(s: seq<bool>, idx: nat) : (r: BV)
        requires idx <= |s|
        requires |s| == WORD_SIZE as nat
        ensures forall i | idx <= i < |s| :: s[i] == BitIsSet(r, i as I)
        //ensures forall i | 0 <= i < idx && Dummy():: !BitIsSet(r, i as I)
        decreases |s| - idx
    {
        if |s| == idx then
            var r := 0;
            assert forall i | idx <= i < |s| :: s[i] == BitIsSet(r, i as I);
            r
        else
            var r := SeqBoolToBitsHelper(s, idx + 1);
            assert forall i | (idx + 1) <= i < |s| :: s[i] == BitIsSet(r, i as I);
            // assert forall i | 0 <= i < AddOne(idx) && Dummy() :: !BitIsSet(r, i as I);
            var res := if s[idx] then BitSetBit(r, idx as I) else BitClearBit(r, idx as I);
            // assume forall i | 0 <= i < idx && Dummy() :: !BitIsSet(res, i as I);
            assert forall i | idx <= i < |s| :: s[i] == BitIsSet(res, i as I) by {

                assert forall i | (idx + 1) <= i < |s| :: s[i] == BitIsSet(r, i as I);
                forall i | (idx + 1) <= i < |s|
                ensures BitIsSet(res, i as I) == BitIsSet(r, i as I) {
                    if s[idx] {
                        lemma_BitSetNotChangeOthers(r, idx as I);
                        lemma_BitClearNotChangeOthers(r, idx as I);
                    } else {
                        lemma_BitSetNotChangeOthers(r, idx as I);
                        lemma_BitClearNotChangeOthers(r, idx as I);
                    }
                    reveal_BitClearBit(); reveal_BitComp();
                    reveal_BitSetBit(); reveal_BitIsSet();
                    reveal_BitAnd(); reveal_BitOr();
                    reveal_Bit();
                }

                forall i |  (idx + 1) <= i < |s|
                ensures s[i] == BitIsSet(res, i as I) {
                    assert i != idx;
                    if s[idx] {
                        lemma_BitSetNotChangeOthers(r, idx as I);
                        lemma_BitClearNotChangeOthers(r, idx as I);
                    } else {
                        lemma_BitSetNotChangeOthers(r, idx as I);
                        lemma_BitClearNotChangeOthers(r, idx as I);
                    }
                    reveal_BitClearBit(); reveal_BitComp();
                    reveal_BitSetBit(); reveal_BitIsSet();
                    reveal_BitAnd(); reveal_BitOr();
                    reveal_Bit();
                    assert BitIsSet(r, i as I) == BitIsSet(res, i as I);
                }
            }
            res
    }

    function {:opaque} SeqBoolToBits(b: seq<bool>) : (r: BV)
        requires |b| == WORD_SIZE as nat
        ensures forall i | InRange(i, |b| as I) :: b[i] == BitIsSet(r, i as I)
    {
        SeqBoolToBitsHelper(b, 0)
    }


    lemma lemma_SeqToBitsToSeq(b: seq<bool>)
        requires |b| == WORD_SIZE as nat
        ensures BitsToSeqBool(SeqBoolToBits(b)) == b
    {
    }

    lemma lemma_BitsToSeqToBits(b: BV)
        ensures SeqBoolToBits(BitsToSeqBool(b)) == b
    {
        var b' := SeqBoolToBits(BitsToSeqBool(b));
        assert forall i | InRange(i, WORD_SIZE) :: (BitIsSet(b', i as I) == BitIsSet(b, i as I));
        lemma_BitEq(b, b');
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

    /// constructs a new bitvector where all its bits are set
    function method {:opaque} BitOnes() : BV {
         0xffff_ffff_ffff_ffff as BV
    }

    /// constructs a new bitvector where none of its bits are set
    function method {:opaque} BitZeros() : BV {
        0x0 as BV
    }

    /// constructs a new bitvector where the first `i` bits are set
    function method {:opaque} BitMask(i: I) : BV
        requires i <= WORD_SIZE
    {
        ((1 as BV) << (i as bv7)) - 1
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Bitwise Operations
    ///////////////////////////////////////////////////////////////////////////////////////////////


    /// tests whether the given bit is true
    predicate method {:opaque} BitIsSet(x:BV, i: I)
        requires i < WORD_SIZE
    {
        // TODO: should we replace this by `BitAnd(x, Bit(i)) == Bit(i)` or BitAnd(x, Bit(i)) != BitZeros()`
        BitAnd(x, Bit(i)) != 0
    }

    function method {:opaque} BitSetBit(x:BV, i: I) : (r: BV)
        requires i < WORD_SIZE
        ensures BitIsSet(r, i)
    {
        reveal_BitIsSet(); reveal_BitAnd(); reveal_BitOr();
        lemma_BitNotZero(i); reveal_BitZeros();

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
        ensures BitAnd(a, BitZeros()) == BitZeros();
    {
        reveal_BitAnd(); reveal_BitZeros();
    }

    /// identity: a & Ones == a
    lemma lemma_BitAndOnes(a: BV)
        ensures BitAnd(a, BitOnes()) == a;
    {
        reveal_BitAnd(); reveal_BitOnes();
    }

    lemma lemma_BitAndOnesEq(a: BV, b: BV)
        ensures (a == b) <==> (BitAnd(a, BitOnes()) == BitAnd(b, BitOnes()))
    {
        reveal_BitAnd();
        reveal_BitOnes();
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
        ensures BitAnd(BitComp(a), a) == BitZeros();
    {
        reveal_BitAnd(); reveal_BitComp(); reveal_BitZeros();
    }

    lemma lemma_BitAndNotSelf(a: BV)
        ensures BitAnd(BitNot(a), a) == 0
    {
        reveal_BitAnd(); reveal_BitNot();
    }

    lemma lemma_BitAndBitDist(a: BV, b: BV, i: I)
        requires i < WORD_SIZE
        ensures (BitAnd(BitAnd(a, Bit(i)), BitAnd(b, Bit(i))) == BitZeros())
                  ==  ((BitAnd(a, Bit(i)) == BitZeros()) || (BitAnd(b, Bit(i)) == BitZeros()))
    {
        reveal_BitAnd(); reveal_Bit(); reveal_BitZeros();
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
            reveal_BitZeros();
            assert BitAnd(BitAnd(a, Bit(i)), BitAnd(b, Bit(i))) == BitZeros() by {
                lemma_BitAndDist(a, b, Bit(i));
            }
            assert (BitAnd(a, Bit(i)) == BitZeros()) || (BitAnd(b, Bit(i)) == BitZeros()) by {
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
        ensures BitOr(a, BitZeros()) == a;
    {
        reveal_BitOr(); reveal_BitZeros();
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
        requires BitOr(a, b) == BitZeros()
        ensures a == BitZeros() && b == BitZeros()
    {
        reveal_BitOr(); reveal_BitZeros();
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
            reveal_BitZeros();
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
        ensures BitXor(a, a) == BitZeros();
    {
        reveal_BitXor(); reveal_BitZeros();
    }

    /// identity: a ^ 0 == a
    lemma lemma_BitXorZero(a: BV)
        ensures BitXor(a, BitZeros()) == a;
    {
        reveal_BitXor(); reveal_BitZeros();
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
        requires BitXor(a, b) == BitZeros()
        ensures a == b
    {
        reveal_BitXor(); reveal_BitZeros();
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

    lemma lemma_BitNotOnes()
        ensures BitNot(BitOnes()) == BitZeros();
        ensures BitNot(BitZeros()) == BitOnes();
    {
        reveal_BitNot(); reveal_BitZeros(); reveal_BitOnes();
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
        ensures Bit(i) != BitZeros()
    {
        reveal_Bit(); reveal_BitZeros();
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
        ensures BitAnd(Bit(i), Bit(j)) == BitZeros();
    {
        reveal_Bit(); reveal_BitAnd(); reveal_BitZeros();
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

    lemma lemma_BitMaskIsOnes()
        ensures BitMask(64) == BitOnes()
    {
        reveal_BitMask(); reveal_BitOnes();
    }

    lemma lemma_BitMaskIsZeros()
        ensures BitMask(0) == BitZeros()
    {
        reveal_BitMask(); reveal_BitZeros();
    }

    lemma lemma_BitMaskExtendBitOr(i: I)
        requires i < WORD_SIZE
        ensures BitMask(i+1) == BitOr(BitMask(i), Bit(i))
    {
        reveal_BitMask(); reveal_BitOr(); reveal_Bit();
    }

    lemma lemma_BitMaskExtendBitOrLess(i: I)
        requires 0 < i <= WORD_SIZE
        ensures BitMask(i) == BitOr(BitMask(i-1), Bit(i-1))
    {
        reveal_BitMask(); reveal_BitOr(); reveal_Bit();
    }

    lemma lemma_BitMaskExtendBitSet(i: I)
        requires i < WORD_SIZE
        ensures BitMask(i+1) == BitSetBit(BitMask(i), i)
    {
        reveal_BitSetBit();
        lemma_BitMaskExtendBitOr(i);
    }

    lemma lemma_BitMaskExtendBitSetLess(i: I)
        requires 0 < i <= WORD_SIZE
        ensures BitMask(i) == BitSetBit(BitMask(i-1), i-1)
    {
        reveal_BitSetBit();
        reveal_BitMask(); reveal_BitOr(); reveal_Bit();
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Setting Individual Bits
    ///////////////////////////////////////////////////////////////////////////////////////////////


    lemma lemma_BitIsSetPrefix(a: BV, b: BV, i: I, i': I)
        requires 0 < i <= WORD_SIZE
        requires i' <= i
        requires (forall j | InRange(j, i) :: (BitIsSet(a, j) == BitIsSet(b, j)))
        ensures  (forall j | InRange(j, i') :: (BitIsSet(a, j) == BitIsSet(b, j)))
    {
        forall j | InRange(j, i') ensures
            (BitIsSet(a, j) == BitIsSet(b, j))
        {
            assert InRange(j, i);
        }
    }

    lemma lemma_AllBitsEqualBVEq_Induct(a: BV, b: BV, i: I)
        requires 0 <= i <= WORD_SIZE
        requires (forall j | InRange(j, i) :: (BitIsSet(a, j) == BitIsSet(b, j)))
        ensures BitAnd(a, BitMask(i)) == BitAnd(b, BitMask(i))
    {
        if i == 0 {
            lemma_BitMaskIsZeros();
            lemma_BitAndZero(a);
            lemma_BitAndZero(b);
        } else {
            lemma_BitIsSetPrefix(a, b, i, i - 1);
            lemma_AllBitsEqualBVEq_Induct(a, b, i- 1);
            lemma_BitAndComm(a, BitMask(i-1));
            lemma_BitAndComm(b, BitMask(i-1));

            assert InRange(i - 1, i);
            assert BitAnd(Bit(i-1), a) == BitAnd(Bit(i-1), b) by {
                reveal_BitIsSet();
                assert (BitAnd(a, Bit(i - 1))) == (BitAnd(b, Bit(i - 1))) by {
                    reveal_BitAnd(); reveal_Bit();
                }
                lemma_BitAndComm(a, Bit(i-1));
                lemma_BitAndComm(b, Bit(i-1));
            }

            lemma_BitAndOrDist(BitMask(i-1), Bit(i-1), a);
            lemma_BitAndOrDist(BitMask(i-1), Bit(i-1), b);
            lemma_BitAndComm(a, BitOr(BitMask(i-1), Bit(i-1)));
            lemma_BitAndComm(b, BitOr(BitMask(i-1), Bit(i-1)));
            lemma_BitMaskExtendBitOrLess(i);
        }
    }

    lemma lemma_AllBitsEqualBVEq(a: BV, b: BV)
        requires (forall j | InRange(j, WORD_SIZE) :: (BitIsSet(a, j) == BitIsSet(b, j)))
        ensures a == b
    {
        lemma_AllBitsEqualBVEq_Induct(a, b, 64);
        lemma_BitMaskIsOnes();
        lemma_BitAndOnes(a);
        lemma_BitAndOnes(b);
    }

    lemma lemma_BitEq(a: BV, b: BV)
        ensures (a == b) == (forall i |  InRange(i, WORD_SIZE):: (BitIsSet(a, i) == BitIsSet(b, i)))
    {
        if (forall i |  InRange(i, WORD_SIZE):: (BitIsSet(a, i) == BitIsSet(b, i))) {
            lemma_AllBitsEqualBVEq(a, b);
        } else {
        }
    }

    lemma lemma_BitSetSelf(a: BV, i: I)
        requires i < WORD_SIZE
        ensures BitIsSet(BitSetBit(a, i), i)
    {
    }

    lemma lemma_BitSetOther(a: BV, i: I, j: I)
        requires i < WORD_SIZE
        requires j < WORD_SIZE
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
        requires i < WORD_SIZE
        requires j < WORD_SIZE
        requires i != j
        ensures BitIsSet(a, j) <==> BitIsSet(BitClearBit(a, i), j)
    {
        reveal_BitIsSet(); reveal_BitClearBit();
        lemma_BitAndAssoc(a, BitComp(Bit(i)), Bit(j));
        lemma_BitCompNotEqual(i, j);
    }

    lemma lemma_BitSetNotChangeOthers(a: BV, i: I)
        requires i < WORD_SIZE
        ensures forall j | InRange(j, WORD_SIZE) && i != j :: BitIsSet(a, j) == BitIsSet(BitSetBit(a, i), j)
    {
        reveal_BitSetBit();
        reveal_BitIsSet();
        reveal_BitAnd();
        reveal_BitOr();
        reveal_Bit();
    }

    lemma lemma_BitClearNotChangeOthers(a: BV, i: I)
        requires i < WORD_SIZE
        ensures forall j | InRange(j, WORD_SIZE) && i != j :: BitIsSet(a, j) == BitIsSet(BitClearBit(a, i), j)
    {
        reveal_BitClearBit();
        reveal_BitIsSet();
        reveal_BitAnd();
        reveal_BitOr();
        reveal_Bit();
        reveal_BitComp();
    }

    lemma lemma_BitToggleNotChangeOthers(a: BV, i: I)
        requires i < WORD_SIZE
        ensures forall j | InRange(j, WORD_SIZE) && i != j :: BitIsSet(a, j) == BitIsSet(BitToggleBit(a, i), j)
    {
        reveal_BitToggleBit();
        if BitIsSet(a, i) {
            lemma_BitClearNotChangeOthers(a, i);
        } else {
            lemma_BitSetNotChangeOthers(a, i);
        }
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

    lemma lemma_BitDeMorgan_NotOr(a: BV, b: BV)
        ensures BitNot(BitOr(a, b)) == BitAnd(BitNot(a), BitNot(b))
    {
        reveal_BitAnd(); reveal_BitNot(); reveal_BitOr();
    }

    lemma lemma_BitDeMorgan_NotAnd(a: BV, b: BV)
        ensures BitNot(BitAnd(a, b)) == BitOr(BitNot(a), BitNot(b))
    {
        reveal_BitAnd(); reveal_BitNot(); reveal_BitOr();
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Others
    ///////////////////////////////////////////////////////////////////////////////////////////////


    lemma lemma_BitCompNotEqual(i: I, j: I)
        requires i != j
        requires i < WORD_SIZE
        requires j < WORD_SIZE
        ensures BitAnd(BitComp(Bit(i)), Bit(j)) == Bit(j)
    {
        reveal_Bit(); reveal_BitAnd(); reveal_BitAnd(); reveal_BitComp();
    }

}
