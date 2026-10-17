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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `newRaft` on the empty storage is the protocol's initial state (`newRaft_post_init`);
the new `RawNode` holds it with nothing handed out. -/
theorem NewRawNode.wp_proof
    (wp_newRaft : newRaft.spec (GF := GF) (hG := hG))
    (wp_softState : raft.softState.spec (GF := GF) (hG := hG))
    (wp_hardState : raft.hardState.spec (GF := GF) (hG := hG)) :
    NewRawNode.spec (GF := GF) (hG := hG) := by
  intro c cv lok si σ hs csm Hvalid Hlok Hsto Hmi Hdpf Hros Hdccv Hmcs Hasync HpvF
    Happ Hprev Hents Hss Hpe Hhs Hvnd Hv0 Hvlen Hc1 Hc2 Hc3 Hal
  wp_start as ⟨Hc, #Hlg, #Hst, HSt, Hinit⟩
  wp_auto
  wp_apply wp_newRaft c cv lok si σ hs csm Hvalid Hlok Hsto Hmi Hdpf Hros Hdccv Hmcs
    (by rw [Hents]; intro k e h; simp at h) Hss Hpe (fun h => absurd Hhs h) (.inl Happ)
    Hvnd Hv0 Hvlen Hc1 Hc2 Hc3 Hal
    $$ [$Hc $Hlg $Hst $HSt $Hinit] as %r %s %cv' ⟨Hphys, Hc, %HAW, %Hpost⟩
  imod rawNodeOwn_of_pts «$r0_ptr» _ $$ «$r0» with «$r0»
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  try wp_auto
  wp_apply wp_softState _ r cv.ID' s $$ Hphys as Hphys
  -- `prevSoftSt` points to a `SoftState` nobody writes again
  ipersist ss
  wp_apply wp_hardState _ r cv.ID' s $$ Hphys as %hp ⟨#Hhp, Hphys⟩
  obtain ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho, Hpv, Hp, Hse, Hue, Hsd, Hcm, Hap, Hun, Hsn, Hsg, Hgh, Hrst,
    Hrpd, Hsdr', Hdom⟩ := Hpost
  have HT : hs.Term' = W64 0 := Hhs.1
  have HV : hs.Vote' = W64 0 := Hhs.2.1
  have Hrel : NStateRel s initPState :=
    newRaft_post_init hs s Hhs ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho⟩ (by rw [Hp, Hprev])
      (by rw [Hse, Hents]) Hue (by rw [Hcm]; simp [committedAfter, Hhs, Hprev]) Hrst Hrpd
  have Hcm0 : s.logst.committed = W64 0 := by
    rw [Hcm]; simp [committedAfter, Hhs, Hprev]
  have Hapg0 : s.logst.applying = W64 0 := by
    rw [Hap, Hprev, Happ]; rfl
  icases ownRaftPhysC_logwf _ r cv.ID' s $$ Hphys with ⟨%Hlw, Hphys⟩
  have Happ0 : s.logst.applied = W64 0 := by
    have H1 := Hlw.1
    rw [Hapg0] at H1
    have := uint_Z_nonneg s.logst.applied
    word
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  iapply HΦ $$ %«$r0_ptr» %interface.nil
  iexists s
  isplitl [«$r0» Hphys]
  · iapply rawNodeFresh_intro «$r0_ptr» cv.ID' si (GMap.listToSet csm.Voters') cv.StepDownOnRemoval'
        s _ _ _ ?_ Hrel ⟨by rw [Ht, HT], by rw [Hv, HV], Hr, Ho, Hrst, Hrpd⟩
        ⟨by rw [Hp, Hprev], by rw [Hse, Hents], Hue, by rw [Hsd, Hents], Hcm0, Happ0, Hapg0, Hun,
          Hsn, Hsg⟩
        Hgh (by rw [Hpv, HpvF]) Hsdr' Hdom
      $$ «$r0» Hphys ss Hhp [] []
    all_goals first
      | iapply ownSlice_nil
      | iapply ownSliceCap_nil
      | (simp only; rw [HAW, Hasync])
  · ipureintro; rfl

end proof

end EtcdGrove
end Perennial
