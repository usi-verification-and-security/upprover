[![Gitter](https://badges.gitter.im/upprover/hifrog-forum.svg)](https://gitter.im/upprover/hifrog-forum?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

HiFrog
=====
[HiFrog](http://verify.inf.usi.ch/hifrog) is an SMT-based Bounded Model Checker that uses function summaries based on interpolation. It allows verification of a C program with multiple user-defined assertions incrementally. 
HiFrog is implemented in C++ and uses the interpolating SMT solver [OpenSMT](https://github.com/usi-verification-and-security/opensmt.git) which is equipped with a flexible interpolation framework for EUF and LRA for computing function summaries.
HiFrog implements a safe-over approximation approach based on Summary and Theory refinement so that lazily chooses an appropriate theory to precisely reason about program properties. 
 
For more info check the project page: http://verify.inf.usi.ch/hifrog


Installation
=====

First, compile [OpenSMT2](https://github.com/usi-verification-and-security/opensmt.git) as a library and 
install it in your system by simply running
```
$ mkdir build; cd build; cmake ..; make install
```

Then compile HiFrog (uses `cmake` as a build system generator) using the following command
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
To see all the commands, type `./hifrog --help`.

See the [manual](http://verify.inf.usi.ch/hifrog/tool-usage) to check different functionalities of HiFrog.


Contact
=====
If you have questions please mail them to me at
sepideh.a65@gmail.com, or to the discussion forum!
