/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 1) (2026-11-11).
`(*Cluster).Events()` (`examples/raft/tracecheck/concurrent.go`): its recorder's events
(`c.rec.Events()`). Its spec is the recorder's (`SyncRecorder.Events.spec`) through the field: given
`c.rec` (read-only), a recorder of the trace `γt` and the caller's view shift at the recorder's half
of the trace, it returns a slice holding the trace `L` at that moment, `Ψ L`, and
`L.length < receiptBound GF`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent

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
abbrev Cluster.Events.spec : Prop :=
  ∀ (c : Loc) (γt : GName) (r : Loc) (Ψ : List TraceEv → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      c.[G.Cluster, go!"rec"] ↦□ r ∗ isSyncRecorder γt r ∗
      (∀ L, traceAuth γt L ={⊤}=∗ traceAuth γt L ∗ Ψ L) }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster.ty
      @!! go!"Events")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ L, traceEventsRep sl L ∗ ⌜L.length < receiptBound GF⌝ ∗ Ψ L }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
