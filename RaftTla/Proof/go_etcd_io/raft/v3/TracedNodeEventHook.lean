/-
Lean-first (no Rocq counterpart). `traceNodeEvent`'s traced statement and its derivation from the
spec: the helper exists in raft's `with_tla` build only (until the two builds were separated, in
`TracedHooksDraft.lean` and `TracedHooks.lean`).
-/
module

public import RaftTla.Proof.go_etcd_io.raft.v3.TracedHooks
public import RaftTla.Spec.go_etcd_io.raft.v3.traceNodeEvent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [StorageModel GF] [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`traceNodeEvent(evt, r)`, traced** (`traceNodeEvent.spec` with the gate): reads the logger;
nil, it returns, giving `Q`; otherwise it reads `r`'s state (`ownRaftPhysCV`, given back) to build
the event, a `NodeEvOf` one, and fires the caller's update with it. -/
abbrev traceNodeEvent.tracedSpec : Prop :=
  ∀ (evt : w64) (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) (Q : IProp GF),
  -- `evt.String()` panics past the event names (review round 1's F1)
  uint.nat evt < evtNames.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗
      ownRaftPhysCV c c.voters r id s ∗ TraceFire s.gh.tr tl (NodeEvOf evt id s c) Q }}
    (App (App (Val #(functions traceNodeEvent [])) (Val #evt)) (Val #r))
  {{ RET #(); ownRaftPhysCV c c.voters r id s ∗ Q }}

theorem traceNodeEvent.tracedSpec_of_spec (h : traceNodeEvent.spec (GF := GF) (hG := hG)) :
    traceNodeEvent.tracedSpec (GF := GF) (hG := hG) := by
  intro evt c r id s tl Q Hevt
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  ihave Hown := trOwn_physLend _ c r id s $$ Hown
  iapply h evt c r id s tl Q _ Hevt $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

end defs

end EtcdGrove
end Perennial
