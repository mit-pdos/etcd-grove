/- Lean-first (no Rocq counterpart).

raft v3.7 (2026-10-16, stage R5): `newRaft` takes `InitialState` in D7's shape (the conf state a
record `csm`); `prevHardSt` is `r.hardState()`, a fresh read-only hard state (`hsRO`), which
`ownRawNode_intro` takes. Since 2026-10-16 (stage R8b) the result is the node open
(`rawNodeFresh`): `RestartNode` closes it with the ghost state, in either mode (the closing was
here until then). -/
module

public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Spec.go_etcd_io.raft.v3.raft__softState
public import Spec.go_etcd_io.raft.v3.raft__hardState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `newRaft`'s postcondition is the restarted follower's protocol state (`restartPState`). -/
private theorem newRaft_post_restart (hs : HardStateM) (σ : StorState) (s : NState) :
    (NStateWf s ∧
     s.term = hs.Term' ∧
     s.vote = hs.Vote' ∧
     s.lead = W64 0 ∧ s.role = .follower ∧
     s.votes = ∅ ∧ s.outbox = []) →
    s.logst.prev = σ.prev →
    s.logst.sents = σ.ents →
    s.logst.uents = [] →
    s.logst.committed = committedAfter σ.prev hs →
    s.rd.states = [] → s.rd.pend = [] →
    NStateRel s (restartPState hs σ) := by
  intro ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho⟩ Hp Hse Hue Hc Hst Hpd
  refine ⟨?_, Hwf⟩
  simp [toPState, restartPState, initPState, Ht, Hv, Hl, Hr, Hvs, Ho, Hp, Hse, Hue, Hc, proleRole,
    rdNL]
  cases h : s.rd
  simp_all

/-- `newRaft` restores the node from the storage; the new `RawNode` holds it with nothing handed
out (`rawNodeAt`). -/
theorem NewRawNode.wp_proof
    (wp_newRaft : newRaft.spec (GF := GF) (hG := hG))
    (wp_softState : raft.softState.spec (GF := GF) (hG := hG))
    (wp_hardState : raft.hardState.spec (GF := GF) (hG := hG)) :
    NewRawNode.spec (GF := GF) (hG := hG) := by
  intro c cv lok si sn σ hs csm R R' cs' Hvalid Hlok Hsto Hmi Hdpf Hros Hdccv Hmcs Hasync
    Hidx Hpend Hfr1 Hfr2 Hfl Hsg Hdt Hwrap Hrec Hhs Happ Hres Hlen
  wp_start as ⟨Hc, #Hlg, HR, #HFI, #HLI, #HInit⟩
  wp_auto
  wp_apply wp_newRaft c cv lok si sn σ hs csm R R' cs' Hvalid Hlok Hsto Hmi Hdpf Hros Hdccv Hmcs
    Hidx Hpend Hfr1 Hfr2 Hfl Hsg Hdt Hwrap Hrec Hhs Happ Hres Hlen
    $$ [$Hc $Hlg $HR $HFI $HLI $HInit] as %r %s %cv' ⟨HR, Hphys, Hc, %HAW, %Hpost⟩
  imod rawNodeOwn_of_pts «$r0_ptr» _ $$ «$r0» with «$r0»
  try wp_auto
  wp_apply wp_softState _ r cv.ID' s $$ Hphys as Hphys
  -- `prevSoftSt` points to a `SoftState` nobody writes again
  ipersist ss
  wp_apply wp_hardState _ r cv.ID' s $$ Hphys as %hp ⟨#Hhp, Hphys⟩
  obtain ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho, Hpv, Hp, Hse, Hue, Hsd, Hcm, Hap, Happ', Hun, Hsn, Hsg', Hlsn, Hgh,
    Hrst, Hrpd, Hsdr', Hdom, Hdtk⟩ := Hpost
  have Hrel : NStateRel s (restartPState hs σ) :=
    newRaft_post_restart hs σ s ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho⟩ Hp Hse Hue Hcm Hrst Hrpd
  icases ownRaftPhysC_logwf _ r cv.ID' s $$ Hphys with ⟨%Hlw, Hphys⟩
  icases ownRaftPhysC_log_same _ r cv.ID' s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hrw, Hlog⟩
  ihave Hphys := Hback $$ Hlog
  iapply HΦ $$ %«$r0_ptr» %interface.nil
  iframe HR
  iexists s
  isplitl [«$r0» Hphys]
  · unfold rawNodeAt
    iexists _, _, _
    simp only [named]
    iframe «$r0» Hphys ss Hhp
    isplitr
    · ipureintro; simp only; rw [HAW, Hasync]
    isplitr
    · simp only; iapply ownSlice_nil
    isplitr
    · simp only; iapply ownSliceCap_nil
    ipureintro
    refine ⟨Hrel, ⟨Ht, Hv, Hr, Ho, Hrst, Hrpd⟩,
      ⟨Hp, Hse, Hue, Hsd, Hcm, Happ', Hap, Hun, Hsn, Hsg', Hdtk⟩, by rw [Hgh], Hpv, Hsdr', Hdom,
      by simp only [hardstateVal, nodeHardstate]; rw [Ht, Hv, Hcm], ?_, ?_⟩
    · simp only [softstateVal, nodeSoftstate]; rw [Hr]; rfl
    · rw [Hue, Hse, Hp] at Hrw
      simp only [List.length_nil] at Hrw
      omega
  isplitr
  · ipureintro; rfl
  ipureintro; exact ⟨Hlsn, by rw [Hgh]⟩

end proof

end EtcdGrove
end Perennial
