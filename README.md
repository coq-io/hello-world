# Hello World
> A Hello World program in Coq.

## Install from OPAM
Make sure you added the [Coq repository](coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-io-hello-world
    helloWorld

## Install from source
Compile the Coq code:

    ./configure.sh
    make

Compile and execute the generated OCaml:

    cd extraction/
    make
    ./main.native
