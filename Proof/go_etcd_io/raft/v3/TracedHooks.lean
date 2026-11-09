/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 2 (2026-11-09): the S5 Draft's traced hook
statements (`TracedHooksDraft.lean`, frozen at tag `trace-check-frozen`) from the hooks' specs, which
are one spec for both modes (the gate `trOwn`, `TraceFire` at the node's mode): each `X.tracedSpec`
follows from `X.spec` by putting raft's state under the gate and taking it back (`trOwn_split`;
`traceInitState`'s lending form by `trOwn_wand`). Not here: `traceCommit.tracedSpec` and
`raft.maybeCommit.tracedSpec` (stated on the capability `trCapB`, at a phase step: the laws'
level, `TracedHooksGlobal.lean`), the message hooks and `raft.send` (Q9, and `send`'s accessor), and
`traceConfChangeEvent` (its spec is the untraced one still).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedHooksDraft
public import Spec.go_etcd_io.raft.v3.traceInitState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem traceNodeEvent.tracedSpec_of_spec (h : traceNodeEvent.spec (GF := GF) (hG := hG)) :
    traceNodeEvent.tracedSpec (GF := GF) (hG := hG) := by
  intro evt c r id s tl Q Hevt
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h evt c r id s tl Q Hevt $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceBecomeFollower.tracedSpec_of_spec (h : traceBecomeFollower.spec (GF := GF) (hG := hG)) :
    traceBecomeFollower.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s tl Q $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceBecomeCandidate.tracedSpec_of_spec (h : traceBecomeCandidate.spec (GF := GF) (hG := hG)) :
    traceBecomeCandidate.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s tl Q $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceBecomeLeader.tracedSpec_of_spec (h : traceBecomeLeader.spec (GF := GF) (hG := hG)) :
    traceBecomeLeader.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s tl Q $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceReady.tracedSpec_of_spec (h : traceReady.spec (GF := GF) (hG := hG)) :
    traceReady.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s tl Q $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceReplicate.tracedSpec_of_spec (h : traceReplicate.spec (GF := GF) (hG := hG)) :
    traceReplicate.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s es dq ents tl Q
  iintro %Φ ⟨#Hpkg, Hes, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s es dq ents tl Q $$ [$Hes $Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hes, Hown, HQ⟩
  iapply HΦ
  iframe Hes HQ
  iapply Hback $$ Hown

theorem traceInitState.tracedSpec_of_spec (h : traceInitState.spec (GF := GF) (hG := hG)) :
    traceInitState.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h r tl s.gh.tr (NodeEvOf (W64 0) id s c) Q (ownRaftPhysCV c c.voters r id s)
    $$ [$Hpkg $Htl Hown $Hfire]
  · iapply trOwn_wand
    iframe Hown
    iintro Hp
    iexists c, id, s
    iframe Hp
    isplitr
    · ipureintro; exact ⟨rfl, fun _ h => h⟩
    iintro Hp; iexact Hp
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

end ghost

end EtcdGrove
end Perennial
