# Hello World
A Hello World program in Coq.

Install the extraction library for Unix effects:

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam install coq:io-effects:unix:ocaml

Compile the Coq code:

    ./configure.sh
    make

Compile and execute the generated OCaml:

    cd extraction/
    make
    ./main.native
