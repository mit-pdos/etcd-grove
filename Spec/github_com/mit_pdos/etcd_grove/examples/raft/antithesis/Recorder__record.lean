/-
Lean-first (no Rocq counterpart). #33 S4, specs first (`notes/antithesis-s4-design.md` §2).

`(*Recorder).record(ev)`: under the lock, append `ev` to the stream. Handed the report's
representation, its receipts (`⧗ ev.weight`, which the lock keeps: the stream's bound) and the
caller's atomic update appending `ev` to the stream (the harness's invariant opened, the report's
refinement step taken), it fires the update at the append (its linearization point), giving the
update the new stream's fit (`Stream.Fits`), and returns the update's `Q` (the trace check's
`SyncRecorder.TraceEvent`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev Recorder.record.spec : Prop :=
  ∀ (γr : GName) (r p : Loc) (ev : AntCheck.Event) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗ isRecorder γr r ∗ AntCheck.eventRO p ev ∗ ⧗ ev.weight ∗
      (AU <{ ∃∃ evs, recAuth (GF := GF) γr evs }> @ ⊤, ∅
        <{ recAuth γr (evs ++ [ev]) ∗ ⌜Stream.Fits GF (evs ++ [ev])⌝, COMM Q }>) }}
    (App (Val (r @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Recorder.ty @!! go!"record")) (Val #p))
  {{ RET #(); Q }}

end spec

end AntHarness
end EtcdGrove
end Perennial
