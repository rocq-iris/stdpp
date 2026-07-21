(** This file provides support for using std++ in combination with the ssreflect
tactics. It patches up some global options of ssreflect. *)
From Stdlib.ssr Require Export ssreflect.
From stdpp Require Export prelude.

(** Restore Rocq's normal "if" scope, ssr redefines it. *)
Global Open Scope general_if_scope.

(** See Rocq issue #5706 *)
Global Set SsrOldRewriteGoalsOrder.

(** Overwrite ssr's [done] tactic with ours *)
Ltac done := stdpp.tactics.done.
