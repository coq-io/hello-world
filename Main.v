Require Import IoEffects.All.
Require Import IoEffectsUnix.All.
Require Import ListString.All.

Import C.Notations.

Definition main : C.t Unix.effects unit :=
  Unix.log (LString.s "Hello world!").
