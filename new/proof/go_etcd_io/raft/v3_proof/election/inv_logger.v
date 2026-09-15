(** * The Logger interface *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** *** Logging and tracing.

    Every [Logger] method used on the election path returns unit and has no
    observable effect.  [Panicf]/[Panic] are only reached on paths shown
    unreachable, so they get the same (vacuously usable) spec. *)
Axiom is_Logger : interface.t_ok → iProp Σ.
Axiom is_Logger_pers : ∀ l, Persistent (is_Logger l).
#[global] Existing Instance is_Logger_pers.

(** The formatting log methods.  Deliberately *not* [Panic]/[Panicf]: those
    do not return, so a path that reaches one has to be shown unreachable
    rather than assumed away. *)
Definition log_methods : list go_string :=
  ["Info"%go; "Infof"%go; "Debug"%go; "Debugf"%go;
   "Warning"%go; "Warningf"%go; "Error"%go; "Errorf"%go].

Axiom wp_Logger__logf : ∀ (l : interface.t_ok) (meth : go_string)
                          (format : go_string) (args : slice.t),
  meth ∈ log_methods →
  {{{ is_Logger l }}}
    #(methods l.(interface.ty) meth l.(interface.v)) #format #args
  {{{ RET #(); True }}}.

End proof.
