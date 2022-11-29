
[![Gitter](https://badges.gitter.im/upprover/upprover-forum.svg)](https://gitter.im/upprover/upprover-forum?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

UpProver
=====
[UpProver](http://verify.inf.usi.ch/upprover) is a Bounded Model Checker that incrementally verifies different revisions of a C program. The key idea in UpProver is reusing efforts from one verification run to another, instead of verifying the full program over and over again. It uses Function Summarization based on Craig interpolation. For both satisfiability solving and interpolation,  UpProver uses the SMT solver [OpenSMT](https://github.com/usi-verification-and-security/opensmt.git) which is equipped with a flexible interpolation framework for EUF and LRA for computing function summaries. UpProver is implemented in C++. It allows verifying user-specified assertions within a predefined bound. hello


Project page: http://verify.inf.usi.ch/upprover


Installation
=====

First, compile [OpenSMT2](https://github.com/usi-verification-and-security/opensmt.git) (branch master the tag `sri-summer-school`) as a library and 
install it in your system by simply running
```
$ mkdir build; cd build; cmake ..; make install
```

Then compile UpProver (uses `cmake` as a build system generator) using the following command
```
$ cd upprover/trunk/cprover; mkdir build; cd build; cmake ..; make
```

### Changing build type
The default build type is RELEASE. Different build types can be configured using cmake variable CMAKE_BUILD_TYPE. For example, to create a debug build use
```
$ cmake -DCMAKE_BUILD_TYPE=Debug ..
```

Usage
=====
To see all the commands, type `./upprover --help`.

Check the [manual](http://verify.inf.usi.ch/upprover/usage) to use UpProver for verifying different revisions of a C program.


Contact
=====
If you have questions please mail them to me at
sepideh.a65@gmail.com, or to the discussion forum!
