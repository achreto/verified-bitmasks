#! /bin/bash

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
#
# SPDX-License-Identifier: MIT
#

#
# Verify a single Dafny fine and all its dependencies.
#

ROOT=$(git rev-parse --show-toplevel)
DAFNY_DIR=${ROOT}/.dafny
DAFNY=${DAFNY_DIR}/dafny/dafny
CPUS=$(nproc)
VERBOSE=${VERBOSE:-0}
TIMELIMIT=20

if [ ! -f ${DAFNY} ]; then
    echo "dafny not found, please run bash tools/install-dafny.sh first"
    exit 1
fi

TRACE=
if [ "$VERBOSE" -eq 1 ]; then
    TRACE="/trace"
fi

# /induction:1 /noNLarith
${DAFNY}  /compile:0 /noCheating:1 /verifyAllModules /separateModuleOutput /vcsCores:${CPUS} /timeLimit:${TIMELIMIT} ${TRACE} "$@"