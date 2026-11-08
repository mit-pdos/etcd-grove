/-
Port of `election_proof/spec_traceReceiveMessage.v` (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `traceReceiveMessage`: reads `r.traceLogger` and returns when it is nil; otherwise sleeps 1ms (`time.Sleep`) and reports the message's receipt. Under `TraceLoggerOk` (increment 1, `notes/trace-validation-hooks.md`: the logger is nil) it
returns at once, owning nothing but the field, shared (`ownRaftPhysC_traceLogger`). Until
2026-11-08 the translated build was the no-op one (`state_trace_nop.go`) and the spec owned
nothing; Draft S4 of `notes/trace-validation-plan.md` widens `TraceLoggerOk` to a logger. -/
abbrev traceReceiveMessage.spec : Prop :=
  ∀ (r : Loc) (mp : Loc) (tl : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ⌜TraceLoggerOk tl⌝ }}
    (App (App (Val #(functions traceReceiveMessage [])) (Val #r)) (Val #mp))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
