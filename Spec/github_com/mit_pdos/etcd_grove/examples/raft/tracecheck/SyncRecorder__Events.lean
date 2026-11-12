/-
Lean-first (no Rocq counterpart). Trace-check's layer D (2026-11-09).

`(*SyncRecorder).Events()` (`examples/raft/tracecheck/concurrent.go`): under the recorder's lock, a
copy of the recorded events. Its spec (S7 (part 1), 2026-11-11; until then it took the client's half
`traceFrag γt L`, which the harness cannot hand over: the simulation's invariant keeps it): the caller's
view shift `∀ L, traceAuth γt L ={⊤}=∗ traceAuth γt L ∗ Ψ L`, run under the lock against the
recorder's half of the trace, so at the trace `L` the copy holds; it returns a slice holding `L`
(`traceEventsRep`, read-only), `Ψ L`, and the event count's bound `traceLenFits GF L` (`L.length <
receiptBound GF`, named since 2026-11-12, `Fits.lean`: the lock holds a time receipt per event). The former form is the case `Ψ L := ⌜L = L0⌝ ∗ traceFrag γt L0`
with the half in the view shift.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Recorder
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Fits

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
  ∀ (γt : GName) (r : Loc) (Ψ : List TraceEv → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      isSyncRecorder γt r ∗ (∀ L, traceAuth γt L ={⊤}=∗ traceAuth γt L ∗ Ψ L) }}
    (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.SyncRecorder.ty
      @!! go!"Events")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ L, traceEventsRep sl L ∗ ⌜traceLenFits GF L⌝ ∗ Ψ L }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
