Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.

(** The classic Hello World program. *)
Definition hello_world (argv : list LString.t) : C.t System.effects unit :=
  System.log (LString.s "Hello world!").

(** Ask for the user name and answer hello. *)
Definition your_name (argv : list LString.t) : C.t System.effects unit :=
  do! System.log (LString.s "What is your name?") in
  let! name := System.read_line in
  match name with
  | None => ret tt
  | Some name => System.log (LString.s "Hello " ++ name ++ LString.s "!")
  end.

(** A concurrent Hello World. May print "Hello World" or "World Hello". *)
Definition concurrent_hello_world (argv : list LString.t)
  : C.t System.effects unit :=
  let! _ : unit * unit := join
    (System.log (LString.s "Hello"))
    (System.log (LString.s "World")) in
  ret tt.

(** Extract the Hello World program to `extraction/main.ml`. Run the `Makefile`
    in `extraction/` to compile it. *)
Definition main := Extraction.run hello_world.
Extraction "extraction/main" main.

(** Specifications. *)
Module Run.
  (** The Hello World program only says hello. *)
  Definition hello_world_ok (argv : list LString.t)
    : Run.t (hello_world argv) tt.
    apply (Run.log_ok (LString.s "Hello world!")).
  Defined.

  (** The Your Name program answers something when you give your name. *)
  Definition your_name_ok (argv : list LString.t) (name : LString.t)
    : Run.t (your_name argv) tt.
    apply (Run.Let (Run.log_ok _)).
    apply (Run.Let (Run.read_line_ok name)).
    apply (Run.log_ok _).
  Defined.

  (** The Your Name program does nothing more in case of error on stdin. *)
  Definition your_name_error (argv : list LString.t)
    : Run.t (your_name argv) tt.
    apply (Run.Let (Run.log_ok _)).
    apply (Run.Let Run.read_line_error).
    apply Run.Ret.
  Defined.

  (** The concurrent Hello World program says both "Hello" and "World". *)
  Definition concurrent_hello_world_ok (argv : list LString.t)
    : Run.t (concurrent_hello_world argv) tt.
    apply (Run.Let (Run.Join
      (Run.log_ok (LString.s "Hello"))
      (Run.log_ok (LString.s "World")))).
    apply Run.Ret.
  Defined.
End Run.
