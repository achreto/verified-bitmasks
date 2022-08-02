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

include "Spec/MachineTypes.s.dfy"
include "BitFields.i.dfy"

module MachineWords {

    import opened MachineTypes
    import B = BitFields

    function IntToUInt64(a: int) : uint64
        requires 0 <= a < UINT64_MAX()
    {
        a as uint64
    }

    function IntToUInt32(a: int) : uint32
        requires 0 <= a < UINT32_MAX()
    {
        a as uint32
    }


    function IntToUInt16(a: int) : uint16
        requires 0 <= a < UINT16_MAX()
    {
        a as uint16
    }

    function IntToUInt8(a: int) : uint8
        requires 0 <= a < UINT8_MAX()
    {
        a as uint8
    }

    function UInt64ToInt(a: uint64) : int { a as int}
    function UInt64ToNat(a: uint64) : int { a as nat}

    function UInt32ToInt(a: uint32) : int { a as int}
    function UInt32ToNat(a: uint32) : int { a as nat}

    function UInt16ToInt(a: uint16) : int { a as int}
    function UInt16ToNat(a: uint16) : int { a as nat}

    function UInt8ToInt(a: uint8) : int { a as int}
    function UInt8ToNat(a: uint8) : int { a as nat}

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Helper Functions
    ///////////////////////////////////////////////////////////////////////////////////////////////

    /// a predicate for the inrange condition of the bits
    /// intended to be used in foralls.
    predicate InRange(i:uint64, n:uint64) {
        0 <= i && i < n
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // From/To Seq<bool>
    ///////////////////////////////////////////////////////////////////////////////////////////////

    function {:opaque} BitwiseToSeqBool(b: uint64) : (r: seq<bool>)
        ensures |r| == B.WORD_SIZE as nat
        ensures forall i | InRange(i, B.WORD_SIZE) :: r[i] == BitwiseGetBit(b, i)
    {
        reveal_BitwiseGetBit();
        B.BitsToSeqBool(B.WordToBits(b))
    }

    function {:opaque} SeqBoolToBitwise(b: seq<bool>) : (r: uint64)
        requires |b| == B.WORD_SIZE as nat
        ensures forall i | InRange(i, |b| as uint64) :: b[i] == BitwiseGetBit(r, i)
    {
        reveal_BitwiseGetBit(); B.reveal_BitsToWord();
        B.lemma_BitsToWordWordToBits(B.SeqBoolToBits(b));
        B.BitsToWord(B.SeqBoolToBits(b))
    }

    lemma lemma_SeqToBitsToSeq(b: seq<bool>)
        requires |b| == B.WORD_SIZE as nat
        ensures BitwiseToSeqBool(SeqBoolToBitwise(b)) == b
    {
    }

    lemma lemma_BitsToSeqToBits(b: uint64)
        ensures SeqBoolToBitwise(BitwiseToSeqBool(b)) == b
    {
        var b' := SeqBoolToBitwise(BitwiseToSeqBool(b));
        assert forall i | InRange(i, B.WORD_SIZE) :: (BitwiseGetBit(b', i) == BitwiseGetBit(b, i));
        lemma_BitwiseEq(b, b');
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Constructor Functions
    ///////////////////////////////////////////////////////////////////////////////////////////////

    /// constructs a new bitvector where the bit `i` is set
    function method {:opaque} BitwiseBit(i: uint64) : uint64
        requires i < B.WORD_SIZE
    {
        B.BitsToWord(B.Bit(i))
    }

    function method BitwiseOnes() : uint64 {
        0xffff_ffff_ffff_ffff as uint64
    }

    function method BitwiseZeros() : uint64 {
        0x0
    }

    function method {:opaque} BitwiseMask(i: uint64) : uint64
        requires i <= B.WORD_SIZE
    {
        B.BitsToWord(B.BitMask(i))
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Single Bit Operations
    ///////////////////////////////////////////////////////////////////////////////////////////////

    predicate method {:opaque} BitwiseGetBit(a: uint64, i: uint64)
        requires i < B.WORD_SIZE
    {
        B.BitIsSet(B.WordToBits(a), i)
    }

    function method {:opaque} BitwiseSetBit(a: uint64, i: uint64) : (r: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseGetBit(r, i)
    {
        var bv_a := B.WordToBits(a);
        var bv_r := B.BitSetBit(bv_a, i);
        var r    := B.BitsToWord(bv_r);

        assert B.BitIsSet(bv_r, i);
        assert BitwiseGetBit(r, i) by {
            reveal_BitwiseGetBit();
            B.lemma_BitsToWordWordToBits(bv_a);
            B.lemma_BitsToWordWordToBits(bv_r);
        }

        r
    }

    function method {:opaque} BitwiseClearBit(a: uint64, i: uint64) : (r: uint64)
        requires i < B.WORD_SIZE
        ensures !BitwiseGetBit(r, i)
    {
        var bv_a := B.WordToBits(a);
        var bv_r := B.BitClearBit(bv_a, i);
        var r    := B.BitsToWord(bv_r);

        assert !B.BitIsSet(bv_r, i);
        assert !BitwiseGetBit(r, i) by {
            reveal_BitwiseGetBit();
            B.lemma_BitsToWordWordToBits(bv_a);
            B.lemma_BitsToWordWordToBits(bv_r);
        }

        r
    }

    function method {:opaque} BitwiseToggleBit(a: uint64, i: uint64) : (r: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseGetBit(r, i) != BitwiseGetBit(a, i)
    {
        if BitwiseGetBit(a, i) then BitwiseClearBit(a, i)
        else BitwiseSetBit(a, i)
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Bitwise Operations
    ///////////////////////////////////////////////////////////////////////////////////////////////

    function method {:opaque} BitwiseAnd(a: uint64, b: uint64) : (r: uint64)
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_r := B.BitAnd(bv_a, bv_b);
        B.BitsToWord(bv_r)
    }

    function method {:opaque} BitwiseOr(a: uint64, b: uint64) : (r: uint64)
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_r := B.BitOr(bv_a, bv_b);
        B.BitsToWord(bv_r)
    }

    function method {:opaque} BitwiseXor(a: uint64, b: uint64) : (r: uint64)
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_r := B.BitXor(bv_a, bv_b);
        B.BitsToWord(bv_r)
    }

    function method {:opaque} BitwiseNot(a: uint64) : (r: uint64)
    {
        var bv_a := B.WordToBits(a);
        var bv_r := B.BitNot(bv_a);
        B.BitsToWord(bv_r)
    }

    function method {:opaque} BitwiseComp(a: uint64) : (r: uint64)
    {
        var bv_a := B.WordToBits(a);
        var bv_r := B.BitComp(bv_a);
        B.BitsToWord(bv_r)
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Shifts
    ///////////////////////////////////////////////////////////////////////////////////////////////

    function method {:opaque} BitwiseLeftShift(a: uint64, i: uint64) : (r: uint64)
        requires i < B.WORD_SIZE
    {
        var bv_a := B.WordToBits(a);
        var bv_r := B.BitLeftShift(bv_a, i);
        B.BitsToWord(bv_r)
    }


    function method {:opaque} BitwiseRightShift(a: uint64, i: uint64) : (r: uint64)
        requires i < B.WORD_SIZE
    {
        var bv_a := B.WordToBits(a);
        var bv_r := B.BitRightShift(bv_a, i);
        B.BitsToWord(bv_r)
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Arithmetic Operations
    ///////////////////////////////////////////////////////////////////////////////////////////////

    function method BitwiseAdd(a: uint64, b:uint64) : uint64
        requires (a as nat) + (b as nat) <= UINT64_MAX()
    {
        a + b
    }

    function method BitwiseSub(a: uint64, b:uint64) : uint64
        requires a >= b
    {
        a - b
    }

    function method BitwiseMul(a: uint64, b:uint64) : uint64
        requires (a as nat) * (b as nat) <= UINT64_MAX()
    {
        a * b
    }

    function method BitwiseDiv(a: uint64, b:uint64) : uint64
        requires b != 0
    {
        a / b
    }

    function method BitwiseMod(a: uint64, b:uint64) : uint64
        requires b != 0
    {
        a % b
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Lemmas and Equalities: AND
    ///////////////////////////////////////////////////////////////////////////////////////////////

    lemma lemma_BitwiseAndSelf(a: uint64)
        ensures BitwiseAnd(a, a) == a
    {
        var bv_a := B.WordToBits(a);
        B.lemma_BitAndSelf(bv_a);
        B.lemma_WordToBitsBitsToWord(a);
        reveal_BitwiseAnd();
    }

    lemma lemma_BitwiseAndZero(a: uint64)
        ensures BitwiseAnd(a, BitwiseZeros()) == BitwiseZeros()
    {
        var bv_a := B.WordToBits(a);
        B.reveal_WordToBits();
        reveal_BitwiseAnd();
        B.lemma_BitAndZero(bv_a);
        B.reveal_BitsToWord();
        B.reveal_BitZeros();
    }

    lemma lemma_BitwiseAndOnes(a: uint64)
        ensures BitwiseAnd(a, BitwiseOnes()) == a
    {
        var bv_a := B.WordToBits(a);
        var bv_1 := B.WordToBits(BitwiseOnes());

        assert bv_1 == B.BitOnes() by {
            B.reveal_WordToBits();
            B.reveal_BitOnes();
        }
        reveal_BitwiseAnd();
        B.lemma_BitAndOnes(bv_a);
        B.lemma_WordToBitsBitsToWord(a);
        B.reveal_WordToBits();
    }

    lemma lemma_BitwiseAndOnesEq(a: uint64, b: uint64)
        ensures (a == b) <==> (BitwiseAnd(a, BitwiseOnes()) == BitwiseAnd(b, BitwiseOnes()))
    {
        lemma_BitwiseAndOnes(a);
        lemma_BitwiseAndOnes(b);
    }

    lemma lemma_BitwiseAndComm(a: uint64, b: uint64)
        ensures BitwiseAnd(a, b) == BitwiseAnd(b, a)
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        reveal_BitwiseAnd();
        B.lemma_BitAndComm(bv_a, bv_b);
    }

    lemma lemma_BitwiseAndAssoc(a: uint64, b: uint64, c: uint64)
        ensures BitwiseAnd(a, BitwiseAnd(b, c)) == BitwiseAnd(BitwiseAnd(a, b), c)
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_c := B.WordToBits(c);

        reveal_BitwiseAnd();
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_a, bv_b));
        B.lemma_BitAndAssoc(bv_a, bv_b, bv_c);
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_b, bv_c));
    }

    lemma lemma_BitwiseAndDist(a: uint64, b: uint64, c: uint64)
        ensures BitwiseAnd(BitwiseAnd(a, b), c) == BitwiseAnd(BitwiseAnd(a, c), BitwiseAnd(b, c))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_c := B.WordToBits(c);

        reveal_BitwiseAnd();
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_a, bv_b));
        B.lemma_BitAndDist(bv_a, bv_b, bv_c);
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_a, bv_c));
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_b, bv_c));
    }

    lemma lemma_BitwiseAndCompSelf(a: uint64)
        ensures BitwiseAnd(BitwiseComp(a), a) == 0
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseAnd();
        reveal_BitwiseComp();
        B.lemma_BitAndCompSelf(bv_a);
        B.lemma_BitsToWordWordToBits(B.BitComp(bv_a));
        B.reveal_BitsToWord();
        B.reveal_BitZeros();
    }

    lemma lemma_BitwiseAndNotSelf(a: uint64)
        ensures BitwiseAnd(BitwiseNot(a), a) == 0
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseAnd();
        reveal_BitwiseNot();

        B.lemma_BitAndNotSelf(bv_a);
        B.lemma_BitsToWordWordToBits(B.BitNot(bv_a));
        B.reveal_BitsToWord();
        B.reveal_BitZeros();
    }

    lemma lemma_BitwiseAndBitDist(a: uint64, b: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures (BitwiseAnd(BitwiseAnd(a, BitwiseBit(i)), BitwiseAnd(b, BitwiseBit(i))) == 0)
                    ==  ((BitwiseAnd(a, BitwiseBit(i)) == 0) || (BitwiseAnd(b, BitwiseBit(i)) == 0))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseAnd(); reveal_BitwiseBit(); B.reveal_WordToBits(); B.reveal_BitsToWord();
        B.lemma_BitsToWordWordToBits(B.Bit(i));
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_a, B.Bit(i))); B.lemma_BitsToWordWordToBits(B.BitAnd(bv_b, B.Bit(i)));
        B.lemma_BitAndBitDist(bv_a, bv_b, i);
        B.reveal_BitZeros();
    }

    lemma lemma_BitwiseAndIsIntersection(a: uint64, b: uint64, i : uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseGetBit(BitwiseAnd(a, b), i) == (BitwiseGetBit(a, i) && BitwiseGetBit(b, i))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseGetBit(); reveal_BitwiseAnd();
        B.lemma_BitAndIsIntersection(bv_a, bv_b, i);
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_a, bv_b));
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Lemmas and Equalities: OR
    ///////////////////////////////////////////////////////////////////////////////////////////////

    lemma lemma_BitwiseOrSelf(a: uint64)
        ensures BitwiseOr(a, a) == a
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseOr();
        B.lemma_BitOrSelf(bv_a);
        B.lemma_WordToBitsBitsToWord(a);
    }

    lemma lemma_BitwiseOrZero(a: uint64)
        ensures BitwiseOr(a, 0) == a
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseOr();
        B.reveal_WordToBits(); B.reveal_BitZeros();
        B.lemma_BitOrZero(bv_a);
        B.lemma_WordToBitsBitsToWord(a);
    }

    lemma lemma_BitwiseOrOnes(a: uint64)
        ensures BitwiseOr(a, BitwiseOnes()) == BitwiseOnes()
    {
        var bv_a := B.WordToBits(a);
        var bv_1 := B.WordToBits(BitwiseOnes());

        assert bv_1 == B.BitOnes() by {
            B.reveal_WordToBits();
            B.reveal_BitOnes();
        }
        reveal_BitwiseOr();
        B.lemma_BitOrOnes(bv_a);
        B.lemma_WordToBitsBitsToWord(BitwiseOnes());
    }

    lemma lemma_BitwiseOrComm(a: uint64, b: uint64)
        ensures BitwiseOr(a, b) == BitwiseOr(b, a)
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        reveal_BitwiseOr();
        B.lemma_BitOrComm(bv_a, bv_b);
    }

    lemma lemma_BitwiseOrAssoc(a: uint64, b: uint64, c: uint64)
        ensures BitwiseOr(a, BitwiseOr(b, c)) == BitwiseOr(BitwiseOr(a, b), c)
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_c := B.WordToBits(c);

        reveal_BitwiseOr();
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_a, bv_b));
        B.lemma_BitOrAssoc(bv_a, bv_b, bv_c);
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_b, bv_c));
    }

    lemma lemma_BitwiseOrDist(a: uint64, b: uint64, c: uint64)
        ensures BitwiseOr(BitwiseOr(a, b), c) == BitwiseOr(BitwiseOr(a, c), BitwiseOr(b, c))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_c := B.WordToBits(c);

        reveal_BitwiseOr();
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_a, bv_b));
        B.lemma_BitOrDist(bv_a, bv_b, bv_c);
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_a, bv_c));
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_b, bv_c));
    }

    lemma lemma_BitwiseOrZeroImpliesArgs(a: uint64, b: uint64)
        requires BitwiseOr(a, b) == 0
        ensures a == 0 && b == 0
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseOr();
        B.reveal_BitsToWord(); B.reveal_WordToBits(); B.reveal_BitZeros();
        B.lemma_BitOrZeroImpliesArgs(bv_a, bv_b);
    }

    lemma lemma_Bitwise1OrIsUnion(a: uint64, b: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseGetBit(BitwiseOr(a, b), i) == (BitwiseGetBit(a, i) || BitwiseGetBit(b, i))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseGetBit(); reveal_BitwiseOr();
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_a, bv_b));
        B.lemma_BitOrIsUnion(bv_a, bv_b, i);
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Lemmas and Equalities: XOR
    ///////////////////////////////////////////////////////////////////////////////////////////////


    lemma lemma_BitwiseXorSelf(a: uint64)
        ensures BitwiseXor(a, a) == 0
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseXor();
        B.reveal_BitsToWord(); B.reveal_BitZeros();
        B.lemma_BitXorSelf(bv_a);
    }

    lemma lemma_BitwiseXorZero(a: uint64)
        ensures BitwiseXor(a, 0) == a
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseXor();
        B.reveal_WordToBits(); B.reveal_BitZeros();
        B.lemma_BitXorZero(bv_a);
        B.lemma_WordToBitsBitsToWord(a);
    }

    lemma lemma_BitwiseXorOnes(a: uint64)
        ensures BitwiseXor(a, BitwiseOnes()) == BitwiseNot(a)
    {
        var bv_a := B.WordToBits(a);
        var bv_1 := B.WordToBits(BitwiseOnes());

        assert bv_1 == B.BitOnes() by {
            B.reveal_WordToBits();
            B.reveal_BitOnes();
        }

        reveal_BitwiseXor(); reveal_BitwiseNot();
        B.lemma_BitXorOnes(bv_a);
        B.lemma_WordToBitsBitsToWord(BitwiseOnes());
    }

    lemma lemma_BitwiseXorComm(a: uint64, b: uint64)
        ensures BitwiseXor(a, b) == BitwiseXor(b, a)
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        reveal_BitwiseXor();
        B.lemma_BitXorComm(bv_a, bv_b);
    }

    lemma lemma_BitwiseXorAssoc(a: uint64, b: uint64, c: uint64)
        ensures BitwiseXor(a, BitwiseXor(b, c)) == BitwiseXor(BitwiseXor(a, b), c)
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_c := B.WordToBits(c);

        reveal_BitwiseXor();
        B.lemma_BitsToWordWordToBits(B.BitXor(bv_a, bv_b));
        B.lemma_BitXorAssoc(bv_a, bv_b, bv_c);
        B.lemma_BitsToWordWordToBits(B.BitXor(bv_b, bv_c));
    }

    lemma lemma_BitwiseXorZeroImpliesArgs(a: uint64, b:uint64)
        requires BitwiseXor(a, b) == 0
        ensures a == b
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseXor();
        B.lemma_WordToBitsBitsToWord(a);
        B.lemma_WordToBitsBitsToWord(b);
        B.reveal_BitZeros();
        assert B.BitXor(bv_a, bv_b) == B.BitZeros() by {
            B.reveal_BitsToWord();
            B.reveal_WordToBits();
        }

        B.lemma_BitXorZeroImpliesArgs(bv_a, bv_b);
    }

    lemma lemma_BitwiseXorIsNotEq(a: uint64, b: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseGetBit(BitwiseXor(a, b), i) == (BitwiseGetBit(a, i) != BitwiseGetBit(b, i))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseGetBit(); reveal_BitwiseXor();
        B.lemma_BitsToWordWordToBits(B.BitXor(bv_a, bv_b));
        B.lemma_BitXorIsNotEq(bv_a, bv_b, i);
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Lemmas and Equalities: Not and Comp
    ///////////////////////////////////////////////////////////////////////////////////////////////

    lemma lemma_BitwiseNotCompEq(a: uint64)
        ensures BitwiseNot(a) == BitwiseComp(a);
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseNot(); reveal_BitwiseComp();
        B.BitNotCompEq(bv_a);
    }

    lemma lemma_BitwiseNotNot(a: uint64)
        ensures BitwiseNot(BitwiseNot(a)) == a;
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseNot();
        B.lemma_BitsToWordWordToBits(B.BitNot(bv_a));
        B.lemma_BitNotNot(bv_a);
        B.lemma_BitsToWordWordToBits(bv_a);
        B.lemma_WordToBitsBitsToWord(a);
    }

    lemma lemma_BitwiseCompComp(a: uint64)
        ensures BitwiseComp(BitwiseComp(a)) == a;
    {
        lemma_BitwiseNotCompEq(a);
        lemma_BitwiseNotCompEq(BitwiseNot(a));
        lemma_BitwiseNotNot(a);
    }

    lemma lemma_BitwiseNotIsNot(a: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseGetBit(BitwiseNot(a), i) == !BitwiseGetBit(a, i)
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseGetBit(); reveal_BitwiseNot();
        B.lemma_BitNotIsNot(bv_a, i);
        B.lemma_BitsToWordWordToBits(B.BitNot(bv_a));
    }


    lemma lemma_BitwiseNotOnes()
        ensures BitwiseNot(BitwiseOnes()) == BitwiseZeros();
        ensures BitwiseNot(BitwiseZeros()) == BitwiseOnes();
    {
        reveal_BitwiseNot();
        B.lemma_BitNotOnes();
        B.reveal_BitNot(); B.reveal_BitZeros(); B.reveal_BitOnes();
        B.reveal_WordToBits(); B.reveal_BitsToWord();
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Shifts
    ///////////////////////////////////////////////////////////////////////////////////////////////

    // TODO


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Constructors
    ///////////////////////////////////////////////////////////////////////////////////////////////


    lemma lemma_BitwiseBitNotZero(i: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseBit(i) != 0
    {
        reveal_BitwiseBit();
        B.reveal_BitsToWord();
        B.lemma_BitNotZero(i);
        B.reveal_BitZeros();
    }

    lemma lemma_BitBitIsSet(i: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseGetBit(BitwiseBit(i), i)
    {
        reveal_BitwiseGetBit();
        reveal_BitwiseBit();
        B.lemma_BitsToWordWordToBits(B.Bit(i));
        B.lemma_BitBitIsSet(i);
    }

    lemma lemma_BitNotSetBits(i: uint64, j: uint64)
        requires i < B.WORD_SIZE
        requires j < B.WORD_SIZE
        requires i != j
        ensures !BitwiseGetBit(BitwiseBit(i), j)
    {
        reveal_BitwiseGetBit();
        reveal_BitwiseBit();
        B.lemma_BitsToWordWordToBits(B.Bit(i));
        B.lemma_BitNotSetBits(i, j);
    }


    lemma lemma_BitwiseNotEqualAndZero(i: uint64, j: uint64)
        requires i != j
        requires i < B.WORD_SIZE
        requires j < B.WORD_SIZE
        ensures BitwiseAnd(BitwiseBit(i), BitwiseBit(j)) == 0
    {
        reveal_BitwiseBit(); reveal_BitwiseAnd();
        B.lemma_BitNotEqualAndZero(i, j);
        B.reveal_BitsToWord();
        B.lemma_BitsToWordWordToBits(B.Bit(i));
        B.lemma_BitsToWordWordToBits(B.Bit(j));
        B.reveal_BitZeros();
    }

    lemma lemma_BitwiseOnesBitIsSet(i: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseGetBit(BitwiseOnes(), i)
    {
        assert (B.WordToBits(BitwiseOnes()) == B.BitOnes()) by  {
            B.reveal_WordToBits(); B.reveal_BitOnes();
        }
        reveal_BitwiseGetBit();
        B.lemma_BitOnesBitIsSet(i);
    }

    lemma lemma_BitwiseZerosNotBitIsSet(i: uint64   )
        requires i < B.WORD_SIZE
        ensures !BitwiseGetBit(BitwiseZeros(), i)
    {
        assert (B.WordToBits(BitwiseZeros()) == B.BitZeros()) by  {
            B.reveal_WordToBits(); B.reveal_BitZeros();
        }
        reveal_BitwiseGetBit();
        B.lemma_BitZerosNotBitIsSet(i);
    }

    lemma lemma_BitwiseMaskIsOnes()
        ensures BitwiseMask(64) == BitwiseOnes()
    {
        reveal_BitwiseMask();
        B.reveal_BitMask();
        B.reveal_BitsToWord(); B.reveal_WordToBits();
        B.reveal_BitOnes();
    }

    lemma lemma_BitwiseMaskIsZeros()
        ensures BitwiseMask(0) == BitwiseZeros()
    {
        reveal_BitwiseMask();
        B.lemma_BitMaskIsZeros();
        B.reveal_BitsToWord(); B.reveal_WordToBits();
        B.reveal_BitZeros();
    }

    lemma lemma_BitwiseMaskExtendBitOr(i: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseMask(i+1) == BitwiseOr(BitwiseMask(i), BitwiseBit(i))
    {
        reveal_BitwiseMask(); reveal_BitwiseOr(); reveal_BitwiseBit();
        B.lemma_BitsToWordWordToBits(B.BitMask(i));
        B.lemma_BitsToWordWordToBits(B.Bit(i));
        B.lemma_BitMaskExtendBitOr(i);
    }

    lemma lemma_BitwiseMaskExtendBitOrLess(i: uint64)
        requires 0 < i <= B.WORD_SIZE
        ensures BitwiseMask(i) == BitwiseOr(BitwiseMask(i-1), BitwiseBit(i-1))
    {
        reveal_BitwiseMask(); reveal_BitwiseOr(); reveal_BitwiseBit();
        B.lemma_BitsToWordWordToBits(B.BitMask(i-1));
        B.lemma_BitsToWordWordToBits(B.Bit(i-1));
        B.lemma_BitMaskExtendBitOrLess(i);
    }

    lemma lemma_BitwiseMaskExtendBitSet(i: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseMask(i+1) == BitwiseSetBit(BitwiseMask(i), i)
    {
        reveal_BitwiseSetBit(); reveal_BitwiseMask();
        B.lemma_BitsToWordWordToBits(B.BitMask(i));
        B.lemma_BitMaskExtendBitSet(i);
    }

    lemma lemma_BitwiseMaskExtendBitSetLess(i: uint64)
        requires 0 < i <= B.WORD_SIZE
        ensures BitwiseMask(i) == BitwiseSetBit(BitwiseMask(i-1), i-1)
    {
        reveal_BitwiseSetBit(); reveal_BitwiseMask();
        B.lemma_BitsToWordWordToBits(B.BitMask(i-1));
        B.lemma_BitMaskExtendBitSetLess(i);
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Setting Individual Bits
    ///////////////////////////////////////////////////////////////////////////////////////////////

    lemma lemma_BitwiseForallImpliesBitForall(a: uint64, b: uint64)
        requires (forall j | InRange(j, B.WORD_SIZE) :: (BitwiseGetBit(a, j) == BitwiseGetBit(b, j)))
        ensures  (forall j | B.InRange(j, B.WORD_SIZE) :: (B.BitIsSet(B.WordToBits(a), j) == B.BitIsSet(B.WordToBits(b), j)))
    {
        forall j | B.InRange(j, B.WORD_SIZE)
        ensures (B.BitIsSet(B.WordToBits(a), j) == B.BitIsSet(B.WordToBits(b), j))
        {
            assert B.InRange(j, B.WORD_SIZE);
            assert InRange(j, B.WORD_SIZE);
            reveal_BitwiseGetBit();
            assert BitwiseGetBit(a, j)  == B.BitIsSet(B.WordToBits(a), j);
            assert BitwiseGetBit(b, j)  == B.BitIsSet(B.WordToBits(b), j);
        }
    }

    lemma lemma_BitwiseAllBitsEqualBVEq(a: uint64, b: uint64)
        requires (forall j | InRange(j, B.WORD_SIZE) :: (BitwiseGetBit(a, j) == BitwiseGetBit(b, j)))
        ensures a == b
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        lemma_BitwiseForallImpliesBitForall(a, b);
        B.lemma_AllBitsEqualBVEq(bv_a, bv_b);
        B.lemma_BitsToWordEq(bv_a, bv_b);
        B.lemma_WordToBitsBitsToWord(a);
        B.lemma_WordToBitsBitsToWord(b);
    }

    lemma lemma_BitwiseEq(a: uint64, b: uint64)
        ensures (a == b) == (forall i |  InRange(i, B.WORD_SIZE):: (BitwiseGetBit(a, i) == BitwiseGetBit(b, i)))
    {
        if (forall i |  InRange(i, B.WORD_SIZE):: (BitwiseGetBit(a, i) == BitwiseGetBit(b, i))) {
            lemma_BitwiseAllBitsEqualBVEq(a, b);
        } else {
        }

    }


    lemma lemma_BitwiseSetSelf(a: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures BitwiseGetBit(BitwiseSetBit(a, i), i)
    {
    }

    lemma lemma_BitwiseSetOther(a: uint64, i: uint64, j: uint64)
        requires i < B.WORD_SIZE
        requires j < B.WORD_SIZE
        requires i != j
        ensures BitwiseGetBit(a, j) <==> BitwiseGetBit(BitwiseSetBit(a, i), j)
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseGetBit(); reveal_BitwiseSetBit();
        B.lemma_BitsToWordWordToBits(B.BitSetBit(bv_a, i));
        B.lemma_BitSetOther(bv_a, i, j);
    }

    lemma lemma_BitwiseClearSelf(a: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures !BitwiseGetBit(BitwiseClearBit(a, i), i)
    {
    }

    lemma lemma_BitwiseClearOther(a: uint64, i: uint64, j: uint64)
        requires i < B.WORD_SIZE
        requires j < B.WORD_SIZE
        requires i != j
        ensures BitwiseGetBit(a, j) <==> BitwiseGetBit(BitwiseClearBit(a, i), j)
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseGetBit(); reveal_BitwiseClearBit();
        B.lemma_BitsToWordWordToBits(B.BitClearBit(bv_a, i));
        B.lemma_BitClearOther(bv_a, i, j);
    }

    lemma lemma_BitwiseSetNotChangeOthers(a: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures forall j | InRange(j, B.WORD_SIZE) && i != j :: BitwiseGetBit(a, j) == BitwiseGetBit(BitwiseSetBit(a, i), j)
    {
        var bv_a := B.WordToBits(a);
        B.lemma_BitSetNotChangeOthers(bv_a, i);

        forall j | InRange(j, B.WORD_SIZE) && i != j
        ensures BitwiseGetBit(a, j) == BitwiseGetBit(BitwiseSetBit(a, i), j)
        {
            reveal_BitwiseGetBit(); reveal_BitwiseSetBit();
            B.lemma_BitsToWordWordToBits(B.BitSetBit(bv_a, i));
        }
    }

    lemma lemma_BitwiseClearNotChangeOthers(a: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures forall j | InRange(j, B.WORD_SIZE) && i != j :: BitwiseGetBit(a, j) == BitwiseGetBit(BitwiseClearBit(a, i), j)
    {
        var bv_a := B.WordToBits(a);
        B.lemma_BitClearNotChangeOthers(bv_a, i);

        forall j | InRange(j, B.WORD_SIZE) && i != j
        ensures BitwiseGetBit(a, j) == BitwiseGetBit(BitwiseClearBit(a, i), j)
        {
            reveal_BitwiseGetBit(); reveal_BitwiseClearBit();
            B.lemma_BitsToWordWordToBits(B.BitClearBit(bv_a, i));
        }
    }

    lemma lemma_BitwiseToggleNotChangeOthers(a: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures forall j | InRange(j, B.WORD_SIZE) && i != j :: BitwiseGetBit(a, j) == BitwiseGetBit(BitwiseToggleBit(a, i), j)
    {
        reveal_BitwiseToggleBit();
        if BitwiseGetBit(a, i) {
            assert BitwiseToggleBit(a, i) == BitwiseClearBit(a, i);
            lemma_BitwiseClearNotChangeOthers(a, i);
        } else {
            assert BitwiseToggleBit(a, i) == BitwiseSetBit(a, i);
            lemma_BitwiseSetNotChangeOthers(a, i);
        }
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Distribution of And/Or
    ///////////////////////////////////////////////////////////////////////////////////////////////

   lemma lemma_BitwiseAndOrDist(a: uint64, b: uint64, c: uint64)
        ensures BitwiseAnd(BitwiseOr(a, b), c) == BitwiseOr(BitwiseAnd(a, c), BitwiseAnd(b, c))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_c := B.WordToBits(c);

        reveal_BitwiseAnd(); reveal_BitwiseOr();
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_a, bv_b));
        B.lemma_BitAndOrDist(bv_a, bv_b, bv_c);
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_a, bv_c));
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_b, bv_c));
    }

    lemma lemma_BitwiseOrAndDist(a: uint64, b: uint64, c: uint64)
        ensures BitwiseOr(BitwiseAnd(a, b), c) == BitwiseAnd(BitwiseOr(a, c), BitwiseOr(b, c))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);
        var bv_c := B.WordToBits(c);

        reveal_BitwiseAnd(); reveal_BitwiseOr();
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_a, bv_b));
        B.lemma_BitOrAndDist(bv_a, bv_b, bv_c);
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_a, bv_c));
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_b, bv_c));
    }

    lemma lemma_BitwiseOrAndSelf(a: uint64, b: uint64)
        ensures BitwiseAnd(BitwiseOr(a, b), b) == b
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseAnd(); reveal_BitwiseOr();
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_a, bv_b));
        B.lemma_WordToBitsBitsToWord(b);
        B.lemma_BitOrAndSelf(bv_a, bv_b);
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // DeMorgan's Laws
    ///////////////////////////////////////////////////////////////////////////////////////////////

    lemma lemma_BitwiseDeMorgan_NotOr(a: uint64, b: uint64)
        ensures BitwiseNot(BitwiseOr(a, b)) == BitwiseAnd(BitwiseNot(a), BitwiseNot(b))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseNot(); reveal_BitwiseOr(); reveal_BitwiseAnd();
        B.lemma_BitsToWordWordToBits(B.BitOr(bv_a, bv_b));
        B.lemma_BitsToWordWordToBits(B.BitNot(bv_a));
        B.lemma_BitsToWordWordToBits(B.BitNot(bv_b));
        B.lemma_BitDeMorgan_NotOr(bv_a, bv_b);
    }

    lemma lemma_BitwiseDeMorgan_NotAnd(a: uint64, b: uint64)
        ensures BitwiseNot(BitwiseAnd(a, b)) == BitwiseOr(BitwiseNot(a), BitwiseNot(b))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseNot(); reveal_BitwiseOr(); reveal_BitwiseAnd();
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_a, bv_b));
        B.lemma_BitsToWordWordToBits(B.BitNot(bv_a));
        B.lemma_BitsToWordWordToBits(B.BitNot(bv_b));
        B.lemma_BitDeMorgan_NotAnd(bv_a, bv_b);
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // Others
    ///////////////////////////////////////////////////////////////////////////////////////////////

    lemma lemma_BitwiseCompNotEqual(i: uint64, j: uint64)
        requires i != j
        requires i < B.WORD_SIZE
        requires j < B.WORD_SIZE
        ensures BitwiseAnd(BitwiseComp(BitwiseBit(i)), BitwiseBit(j)) == BitwiseBit(j)
    {
        reveal_BitwiseAnd(); reveal_BitwiseComp(); reveal_BitwiseBit();
        B.lemma_BitsToWordWordToBits(B.Bit(i));
        B.lemma_BitsToWordWordToBits(B.Bit(j));
        B.lemma_BitsToWordWordToBits(B.BitComp(B.Bit(i)));
        B.lemma_BitCompNotEqual(i, j);
    }
}
