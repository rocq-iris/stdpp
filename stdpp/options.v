(** Iris sets some Rocq flags for itself that we do not want to impose on
downstream clients by default. Those flags are configured in [config/flags] so
they are set as command-line parameters in our Rocq invocations. This file
exists as an old deprecated way to achieve the same effect: [Import]ing this
file sets these flags without leaking them to downstream clients.
Please do not import this file into new projects; instead, copy-paste the
[-set] flags from [config/flags] into your [_RocqProject] (with [-arg]). *)

(* Everything here should be [Export Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)

(** Allow async proof-checking of sections. *)
#[export] Set Default Proof Using "Type".

(** Enforces that every tactic is executed with a single focused goal, meaning
that bullets and curly braces must be used to structure the proof. *)
#[export] Set Default Goal Selector "!".
