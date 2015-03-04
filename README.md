# Hello World
A Hello World program in Coq.

## Run
Install the extraction library for System effects:

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam install -j4 coq:io:system

Compile the Coq code:

    ./configure.sh
    make

Compile and execute the generated OCaml:

    cd extraction/
    make
    ./main.native
