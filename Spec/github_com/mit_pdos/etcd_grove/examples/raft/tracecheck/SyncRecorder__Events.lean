/-
Lean-first (no Rocq counterpart). Trace-check's layer D (2026-11-09).

`(*SyncRecorder).Events()` (`examples/raft/tracecheck/concurrent.go`): under the recorder's lock, a
copy of the recorded events. Its spec: given the client's half of the trace, `traceFrag γt L`
(which fixes the trace, as the lock's half agrees with it), it returns a slice holding `L`
(`traceEventsRep`, read-only), and the half back.
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
abbrev SyncRecorder.Events.spec : Prop :=
  ∀ (γt : GName) (r : Loc) (L : List TraceEv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      isSyncRecorder γt r ∗ traceFrag γt L }}
    (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder.ty
      @!! go!"Events")) (Val #()))
  {{ (sl : GoSlice), RET #sl; traceFrag γt L ∗ traceEventsRep sl L }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
