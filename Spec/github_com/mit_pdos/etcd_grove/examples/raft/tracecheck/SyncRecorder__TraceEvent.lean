/-
Lean-first (no Rocq counterpart). Trace-check's layer D (2026-11-09).

`(*SyncRecorder).TraceEvent(ev)` (`examples/raft/tracecheck/concurrent.go`): under the recorder's
lock, append a copy of `*ev` to the recorded events. Its spec is raft's side of the logger contract
(`isTraceLogger`, `InvTrace.lean`) for the recorder: handed the event's representation and the
caller's atomic update appending `e` to the trace, it fires the update (its linearization point,
the append under the lock) and returns with the update's `Q`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Recorder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- See the file header. -/
abbrev SyncRecorder.TraceEvent.spec : Prop :=
  ∀ (γt : GName) (r p : Loc) (e : TraceEv) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      isSyncRecorder γt r ∗ tracingEventRep p e ∗
      (AU <{ ∃∃ L, traceAuth (GF := GF) γt L }> @ ⊤, ∅ <{ traceAuth γt (L ++ [e]), COMM Q }>) }}
    (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder.ty
      @!! go!"TraceEvent")) (Val #p))
  {{ RET #(); Q }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
