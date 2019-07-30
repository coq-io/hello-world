# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/megaphone-48.png) Hello World
> A Hello World program in Coq.

[![build status](https://img.shields.io/travis/coq-io/hello-world.svg)](https://travis-ci.org/coq-io/hello-world)

## Install from opam
Make sure you added the [Coq repository](https://github.com/coq/opam-coq-archive):

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
