/-
Port of `election_proof/spec_traceReady.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `traceReady`: reports `Ready` through `traceNodeEvent` (`traceEvent`), which reads `r.traceLogger` first. Under `TraceLoggerOk` (increment 1, `notes/trace-validation-hooks.md`: the logger is nil) it
returns at once, owning nothing but the field, shared (`ownRaftPhysC_traceLogger`). Until
2026-11-08 the translated build was the no-op one (`state_trace_nop.go`) and the spec owned
nothing; Draft S4 of `notes/trace-validation-plan.md` widens `TraceLoggerOk` to a logger. -/
abbrev traceReady.spec : Prop :=
  ∀ (r : Loc) (tl : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ⌜TraceLoggerOk tl⌝ }}
    (App (Val #(functions traceReady [])) (Val #r))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
