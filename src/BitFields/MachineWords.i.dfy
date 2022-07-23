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
        var bv_a := B.WordToBits(a);
        var bv_r := B.BitToggleBit(bv_a, i);
        var r    := B.BitsToWord(bv_r);

        assert B.BitIsSet(bv_a, i) != B.BitIsSet(bv_r, i);

        assert BitwiseGetBit(r, i) != BitwiseGetBit(a, i) by {
            reveal_BitwiseGetBit();
            B.lemma_BitsToWordWordToBits(bv_a);
            B.lemma_BitsToWordWordToBits(bv_r);
        }

        r
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
        ensures BitwiseAnd(a, 0) == 0
    {
        var bv_a := B.WordToBits(a);
        B.reveal_WordToBits();
        reveal_BitwiseAnd();
        B.lemma_BitAndZero(bv_a);
        B.reveal_BitsToWord();
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
    }

    lemma lemma_BitwiseAndBitDist(a: uint64, b: uint64, i: uint64)
        requires i < B.WORD_SIZE
        ensures (BitwiseAnd(BitwiseAnd(a, BitwiseBit(i)), BitwiseAnd(b, BitwiseBit(i))) == 0)  ==  ((BitwiseAnd(a, BitwiseBit(i)) == 0) || (BitwiseAnd(b, BitwiseBit(i)) == 0))
    {
        var bv_a := B.WordToBits(a);
        var bv_b := B.WordToBits(b);

        reveal_BitwiseAnd(); reveal_BitwiseBit(); B.reveal_WordToBits(); B.reveal_BitsToWord();
        B.lemma_BitsToWordWordToBits(B.Bit(i));
        B.lemma_BitsToWordWordToBits(B.BitAnd(bv_a, B.Bit(i))); B.lemma_BitsToWordWordToBits(B.BitAnd(bv_b, B.Bit(i)));
        B.lemma_BitAndBitDist(bv_a, bv_b, i);
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
        B.reveal_WordToBits();
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
        B.reveal_BitsToWord();
        B.reveal_WordToBits();
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
        B.reveal_BitsToWord();
        B.lemma_BitXorSelf(bv_a);
    }

    lemma lemma_BitwiseXorZero(a: uint64)
        ensures BitwiseXor(a, 0) == a
    {
        var bv_a := B.WordToBits(a);

        reveal_BitwiseXor();
        B.reveal_WordToBits();
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
        assert B.BitXor(bv_a, bv_b) == 0 by {
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

}
