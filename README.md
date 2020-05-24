# Automatic Design of Algorithms Through Evolution (ADATE)

Automatic Design of Algorithms Through Evolution (ADATE) is a system for automatic programming, i.e., inductive inference of algorithms. ADATE can automatically generate non-trivial and novel algorithms. Algorithms are generated through large-scale combinatorial search that employs sophisticated program transformations.

## Introduction

ADATE was written by [Roland Olsson](https://www.hiof.no/it/personer/und-forsk-ansatte/rolando/) and originally posted at:
https://web.archive.org/web/20180506202119/http://www-ia.hiof.no/~rolando/adate_intro.html

As the website is no longer active and it appears as though this software is only accessible in limited form via the Web Archive, it has been mirrored here for continuity.

Please see `AdateManual.pdf` for a detailed description of how this software works and how to use it.

## Setup

ADATE requires a number of dependencies and, in particular, a 32-bit operating system. This is due to the fact that the `makespec` program was only accessible via a compiled binary, and had been compiled on a 32-bit Linux system. This can typically be accomplished via a VM.

If you are on Windows, note that Windows Subsystem for Linux only supports 64-bit instructions, but you can use a 32-bit version of Linux with Windows Subsystem for Linux 2. You would just need to install the appropriate libs by running:

```
sudo dpkg --add-architecture i386
sudo apt-get update
```

You may retrieve MLton from:
http://mlton.org/

Supplemental tools See5 and C5.0 are discussed at:
https://www.rulequest.com/see5-info.html

The code itself points to paths that were specific to the system that ADATE had been developed on. Files with paths that need to be modified for the specific user:

* mlt
* mltmpi
* mlton
* sml

The general compilation process, as outlined in the provided PDF manual, is to build a `.spec` file indicating what functions and inputs you would like, and then running the following commands:

```
./makespec <file>.spec
cat main1.sml <file>.spec.sml main2.sml > main.sml
./mlt
./main start
```

See the PDF for more details on how to pause and resume running the program after starting it.

## Example

An example of how to use this software can be seen with the provided SEQ files and the corresponding PDF `NumberSequenceSolver.pdf` which, as its name implies, solves number sequences using genetic programming.

Each `SEQ0X.spec` file indicates a different number sequence. To run the first one, for example, you may use the following commands:

```
./makespec SEQ01.spec
cat main1.sml SEQ01.spec.sml main2.sml > main.sml
./mlt
./main start
```

## Older Versions

The most recent available version of ADATE is version 0.50. Older versions have been provided for historical purposes.

### 0.41

Version 0.41 includes the source code for the makespec binary and may be used to produce a build compatile with 64-bit systems in the absence of source code for makespec in version 0.50.

### 0.30

Version 0.30 has also been provided. This is a Windows build of ADATE. Special thanks to Massimo Dentico for providing me with a copy of this version, as the Windows build was unavailable via the Archive.org Wayback Machine.

This version requires SML/NJ to be installed on your system. You may download the latest version from the SML/NJ website:

https://www.smlnj.org/

As of writing, the latest version is 110.97, which may be downloaded from:

http://smlnj.cs.uchicago.edu/dist/working/110.97/smlnj-110.97.msi

To use this version of ADATE in Windows, you may simply run `adate.bat` from the command line after installing SML/NJ. You will then be brought into the ADATE session where subsequent commands may be run.

To see an example of defining a specification file and running a session, consult the user guide `v0.30/user-manual.pdf` for more information.

## TODO

* Remove the hardcoded paths so that setup is simpler and takes less time.
* Add support for 64-bit systems.
