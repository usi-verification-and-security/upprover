
About
=====

TODO: write something about hifrog

Using Z3 as backend
====================
If you want to build HiFrog with Z3 available as a backend solver, you need to set CMake option USE_Z3 to ON (default is OFF).
This can be done when populating you build directory adding -DUSE_Z3=ON to cmake command, e.g. `cmake -DUSE_Z3=ON ..`
or later changing the value in cache either manually or using ccmake.

CMake will now look for Z3 cmake package file on your system. This file is automatically exported when Z3 is build using CMake and installed on your system. It is known to work with Z3 version 4.7.1.
