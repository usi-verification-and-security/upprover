

[![Gitter](https://badges.gitter.im/usi-verification-and-security/upprover.svg)](https://gitter.im/usi-verification-and-security/upprover?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

UpProver
=====
[UpProver](http://verify.inf.usi.ch/upprover) is a a Bounded Model Checker that incrementally verifies C program revisions that are closely-related, instead of verifying the full program over and over again. 
It exploits tree-interpolation algorithms in SMT to summarize functions as their behavior relevant to a property in a reusable, localized form. 
It allows verifying user-specified assertions. The verification is performed by unwinding the loops in the program and passing the resulting equation to SMT solver OpenSMT.




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
$ mkdir build; cd build; cmake ..; make
```

### Changing build type
The default build type is RELEASE. Different build type can be configured using cmake variable CMAKE_BUILD_TYPE. For example, to create a debug build use
```
$ cmake -DCMAKE_BUILD_TYPE=Debug ..
```

## Contact
If you have questions please mail them to me at
sepideh.a65@gmail.com, or to the discussion forum!
