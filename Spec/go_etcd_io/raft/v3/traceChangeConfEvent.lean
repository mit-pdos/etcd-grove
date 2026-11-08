/- `traceChangeConfEvent` (`state_trace_nop.go`), Lean-first (2026-10-13). -/
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

/-- `traceChangeConfEvent(cci, r)`, `stepLeader`'s hook for an accepted conf change: before
reading the logger it converts the change (`cci.AsV2()`, which for a `*ConfChange` allocates a
fresh `*ConfChangeV2`), reads its changes (`GetType`, `GetNodeId`) and formats them
(`strconv.FormatUint`); the change is only read. Under `TraceLoggerOk` (increment 1, `notes/trace-validation-hooks.md`: the logger is nil) no
event is reported. Until 2026-11-08 the translated build was the no-op one (`state_trace_nop.go`)
and the spec owned nothing; Draft S4 of `notes/trace-validation-plan.md` widens `TraceLoggerOk`
to a logger. -/
abbrev traceChangeConfEvent.spec : Prop :=
  ∀ (c : GoInterface) (dq : DFrac) (o : ConfChangeIM) (r : Loc) (tl : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownConfChangeI c dq (some o) ∗
      r.[raft, go!"traceLogger"] ↦□ tl ∗ ⌜TraceLoggerOk tl⌝ }}
    (App (App (Val #(functions traceChangeConfEvent [])) (Val #c)) (Val #r))
  {{ RET #(); ownConfChangeI c dq (some o) }}

end spec

end EtcdGrove
end Perennial
