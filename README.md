This agda project allows you to use a simple FRP library to construct
and simulate light show sequences for strings of RGB leds.

It does not control actual lights, but it does render the lights using OpenGL.

To build this you will first need to 'cabal install GLFW-b'

You will also need to install the agda stdlib and the agda-lib-ffi Haskell library.

Then you can hopefully build the whole thing with something like:

agda -i../../../agda/lib-0.7/src -i. --compile Main.agda
