#
# MIT License
#
# Copyright (c) 2022 Reto Achermann, The University of British Columbia
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.


BITFIELDS_SPEC =
BITFIELDS += src/BitFields/BitFields.i.dfy
BITFIELDS += src/BitFields/MachineWords.i.dfy

BITFIELDSLOGS=$(patsubst %.dfy,target/logs/%.log,$(BITFIELDS))


BITMASK_SPEC =
BITMASK += src/BitMask/BitmaskArray.i.dfy
BITMASK += src/BitMask/BitmaskSeq.i.dfy

BITMASK_LOGS=$(patsubst %.dfy,build/verify/%.log,$(BITMASK))

DFY_VERIFY  = $(BITFIELDS) $(BITFIELDS_SPEC) $(BITMASK) $(BITMASK_SPEC)
DFY_COMPILE = $(BITMASK) $(BITFIELDS)

# verify the files
verify: $(patsubst src/%.dfy,build/verify/%.log,$(DFY_VERIFY))
	@echo "Verified..."

# generate the cpp code
generate: $(patsubst src/%.dfy,build/generated/%.cpp,$(DFY_COMPILE))
	@echo "Generated"


# Rule to verify a dafny file
build/verify/%.i.log : src/%.i.dfy
	@mkdir -p $(@D)
	VERBOSE=1 bash tools/dafny-verify-all.sh $< > $@

# Rule to generate the CPP file from the dafny file
build/generated/%.i.cpp : src/%.i.dfy build/verify/%.i.log
	@mkdir -p $(@D)
	bash tools/dafny-compile.sh $< $@

clean :
	rm -rf build