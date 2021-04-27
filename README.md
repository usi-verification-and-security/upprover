

[![Gitter](https://badges.gitter.im/usi-verification-and-security/upprover.svg)](https://gitter.im/usi-verification-and-security/upprover?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge) [![Join the chat at https://gitter.im/usi-verification-and-security/upprover-forum](https://badges.gitter.im/usi-verification-and-security/upprover-forum.svg)](https://gitter.im/usi-verification-and-security/upprover-forum?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

UpProver
=====
[UpProver](http://verify.inf.usi.ch/upprover) is a a Bounded Model Checker that incrementally verifies C program revisions that are closely-related, instead of verifying the full program over and over again. It allows verifying user-specified assertions within a predefined bound. UpProver is implemented in C++ and uses the interpolating SMT solver [OpenSMT](https://github.com/usi-verification-and-security/opensmt.git) which is used for both satisfiability solving and interpolation for computing function summaries.



Project page: http://verify.inf.usi.ch/upprover


Installation
=====

First compile [OpenSMT2](https://github.com/usi-verification-and-security/opensmt.git) as a library and 
install it in your system by simply runing
```
$ mkdir build; cd build; cmake ..; make install
```

Then compile UpProver (uses `cmake` as a build system generator) using the following command
```
$ cd hifrog/trunk/cprover; mkdir build; cd build; cmake ..; make
```

### Changing build type
The default build type is RELEASE. Different build type can be configured using cmake variable CMAKE_BUILD_TYPE. For example, to create a debug build use
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
