# Hello World

[![Join the chat at https://gitter.im/clarus/coq-hello-world](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/clarus/coq-hello-world?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
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
