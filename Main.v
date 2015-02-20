Require Import IoEffects.All.
Require Import IoEffectsUnix.All.
Require Import ListString.All.

Import C.Notations.

Definition hello_world : C.t Unix.effects unit :=
  Unix.log (LString.s "Hello world!").

Definition hello_world_ok : Run.t hello_world tt.
  apply (Run.log_ok (LString.s "Hello world!")).
Defined.

Definition main := Extraction.Lwt.run (Extraction.eval hello_world).
Extraction "extraction/main" main.
