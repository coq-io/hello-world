Require Import Coq.Lists.List.
Require Import IoEffects.All.
Require Import IoEffectsUnix.All.
Require Import ListString.All.

Import ListNotations.
Import C.Notations.

(** The classic Hello World program. *)
Definition hello_world : C.t Unix.effects unit :=
  Unix.log (LString.s "Hello world!").

(** Ask for the user name and answer hello. *)
Definition your_name : C.t Unix.effects unit :=
  do! Unix.log (LString.s "What is your name?") in
  let! name := Unix.read_line in
  match name with
  | None => ret tt
  | Some name => Unix.log (LString.s "Hello " ++ name ++ LString.s "!")
  end.

(** Extract the Hello World program to `extraction/main.ml`. Run the `Makefile`
    in `extraction/` to compile it. *)
Definition main := Extraction.Lwt.run (Extraction.eval hello_world).
Extraction "extraction/main" main.

(** Specifications. *)
Module Run.
  (** The Hello World program only says hello. *)
  Definition hello_world_ok : Run.t hello_world tt.
    apply (Run.log_ok (LString.s "Hello world!")).
  Defined.

  (** The Your Name program answers something when you give your name. *)
  Definition your_name_ok (name : LString.t) : Run.t your_name tt.
    apply (Run.Let (Run.log_ok _)).
    apply (Run.Let (Run.read_line_ok name)).
    apply (Run.log_ok _).
  Defined.

  (** The Your Name program does nothing more in case of error on stdin. *)
  Definition your_name_error : Run.t your_name tt.
    apply (Run.Let (Run.log_ok _)).
    apply (Run.Let Run.read_line_error).
    apply Run.Ret.
  Defined.
End Run.
