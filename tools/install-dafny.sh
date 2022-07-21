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

# Script to download and install Dafny.
#
# see: https://github.com/dafny-lang/dafny/releases/latest

set -e

DAFNY_RELEASE=https://github.com/dafny-lang/dafny/releases/download/v3.7.3/dafny-3.7.3-x64-ubuntu-16.04.zip

ROOT=$(git rev-parse --show-toplevel)
DAFNY_DIR=${ROOT}/.dafny

# create the dafny directory
mkdir -p ${DAFNY_DIR}

# download the file
wget -O ${DAFNY_DIR}/dafny.zip ${DAFNY_RELEASE}

# unzip it
pushd ${DAFNY_DIR}
unzip dafny.zip
popd

# clean up
rm -rf ${DAFNY_DIR}/dafny.zip
