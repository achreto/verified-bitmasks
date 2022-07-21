# Verified Bitmasks

This repository contains verified bitmask implementations in Dafny.

## LICENSE

see LICENSE file.

## Authors

Reto Achermann

## Dependencies

To verify and run the code install [Dafny](https://github.com/dafny-lang/dafny/wiki/INSTALL)

```
$ bash tools/install-dafny.sh
```

The script will install Dafny in the `.dafny` directory of this repository.

Alternatively, you can also use the Visual Studio Code extension.

## Building and Verifying

 - TODO: how to run the full verification, and build it. (Makefile)


## Development

**Verifying**
To verity a Dafny file, you can use the Visual Studio Code plugin or call Dafny on the
file to verify using the following script:

```
$ bash tools/dafny-verify.sh <FILE>
```

**Code Genereation**
To generate code execute the following script, where `TARGET` specifies the language.

```
$ TARGET=xxx bash tools/dafny-compile.sh <FILE>
```

where `TARGET` is one of the languages supported by Dafny. (cpp, cs, python, ...)

