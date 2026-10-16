/- Lean-first (no Rocq counterpart).

raft v3.7 (2026-10-16, stage R5): `newRaft` takes `InitialState` in D7's shape (the conf state a
record `csm`); `prevHardSt` is `r.hardState()`, a fresh read-only hard state (`hsRO`), which
`ownRawNode_intro` takes. -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.NewRawNode
public import Raft37.Spec.go_etcd_io.raft.v3.raft__softState
public import Raft37.Spec.go_etcd_io.raft.v3.raft__hardState

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
  intro γ md c cv lok si σ hs csm Hvalid Hlok Hsto Hmi Hcq Hdpf Hros Hdccv Hmcs Hasync HpvF
    Happ Hprev Hents Hss Hpe Hhs Hvne Hvnd Hv0 Hvlen Hc1 Hc2 Hc3 Hal Hcfg Hid Hsdon
  wp_start as ⟨Hc, #Hlg, #Hst, HSt, #Hinit, Hghost, #Hcomm⟩
  wp_auto
  wp_apply wp_newRaft c cv lok si σ hs csm Hvalid Hlok Hsto Hmi Hcq Hdpf Hros Hdccv Hmcs
    (by rw [Hents]; intro k e h; simp at h) Hss Hpe (fun h => absurd Hhs h) (.inl Happ)
    Hvne Hvnd Hv0 Hvlen Hc1 Hc2 Hc3 Hal
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
  have Hrel : NStateRel s initPState :=
    newRaft_post_init hs s Hhs ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho⟩ (by rw [Hp, Hprev])
      (by rw [Hse, Hents]) Hue (by rw [Hcm]; simp [committedAfter, Hhs, Hprev]) Hrst Hrpd
  icases ownRaftPhysC_sdr _ r cv.ID' s $$ Hphys with ⟨#Hsd0, Hphys⟩
  icases ownRaftPhysC_logwf _ r cv.ID' s $$ Hphys with ⟨%Hlw, Hphys⟩
  have Hdlen0 : ([] : List raftpb.Entry).length = (uint.Z s.logst.applying).toNat := by
    rw [Hap, Hprev, Happ]; rfl
  cases md with
  | static =>
    iunfold rnInit at Hghost
    ihave #Hsdr : sdrOk (GF := GF) r RNMode.static $$ []
    · iunfold sdrOk; iexists s.sdr; iframe Hsd0; ipureintro; intro h; cases h
    ihave Hphys := ownRaftPhysC_toS $$ Hphys
    ihave Hphys : ownRaftPhys γ.reCfg r cv.ID' s $$ [Hphys]
    · rw [Hcfg]; iexact Hphys
    iapply HΦ $$ %«$r0_ptr» %interface.nil
    isplitl
    · iapply ownRawNode_intro_static γ «$r0_ptr» cv.ID'
        { delivered := [], unpersisted := [], steps := [], term := W64 0,
          storage := interface.ok si, mode := .static,
          cfg := cfgState (GMap.listToSet csm.Voters') ∅ }
        s initPState _ _ _ [] rfl Hrel
        (by rw [Hcfg]; exact (GMap.elem_of_list_to_set _ _).2 Hid) ?_
        Hdlen0 (by rw [Hun]) Hsn trivial
        (by rw [Ht, HT]) (by rw [Hsg]) (by rw [Hpv, HpvF]) (by rw [Hgh]) (by rw [Hgh])
        (uint_Z_nonneg _)
        $$ «$r0» Hphys Hghost Hsdr ss Hhp [] [] [] Hcomm []
      all_goals first
        | (rw [Hsd, Hents]; iapply storedRecs_nil)
        | iapply ownSlice_nil
        | iapply ownSliceCap_nil
        | iempintro
        | iapply pendList_nil
        | (simp only; rw [HAW, Hasync])
    ipureintro; rfl
  | dyn dec c0 h0 h1 =>
    iunfold rnInit at Hghost
    icases Hghost with ⟨%HD, Hgr⟩
    obtain ⟨HD, rfl⟩ := HD
    ihave #Hsdr : sdrOk (GF := GF) r (RNMode.dyn dec (cfgState (GMap.listToSet csm.Voters') ∅) h0 h1)
      $$ []
    · iunfold sdrOk; iexists s.sdr; iframe Hsd0; ipureintro; intro _; rw [Hsdr']; exact Hsdon rfl
    have Happ0 : s.logst.applied = W64 0 := by
      have Hz : uint.Z s.logst.applying = 0 := by
        have := Hdlen0; simp only [List.length_nil] at this
        have := uint_Z_nonneg s.logst.applying; omega
      have H1 := Hlw.1
      have : uint.Z s.logst.applied = 0 := by
        have := uint_Z_nonneg s.logst.applied; omega
      word
    have Hro : rOf s ⟨0, cfgState (GMap.listToSet csm.Voters') ∅, []⟩ =
        rinit (cfgState (GMap.listToSet csm.Voters') ∅) := by
      unfold rOf rinit pciR
      rw [Hrel.1, Happ0, Hsn]
      simp [Hr]
    have Hdiff : domSet s.progress \ GMap.listToSet csm.Voters' = ∅ := by
      rw [Hdom]
      apply GMap.set_eq; intro k
      rw [GMap.elem_of_difference]
      constructor
      · rintro ⟨h1, h2⟩; exact absurd h1 h2
      · intro h; exact absurd h (GMap.not_elem_of_empty _)
    ihave Hghost : ownStepGhost γ
        (RNMode.toG (.dyn dec (cfgState (GMap.listToSet csm.Voters') ∅) h0 h1)
          ⟨0, cfgState (GMap.listToSet csm.Voters') ∅, []⟩)
        (CfgM.simple (GMap.listToSet csm.Voters') (domSet s.progress \ GMap.listToSet csm.Voters'))
        cv.ID' s $$ [Hgr]
    · simp only [RNMode.toG]
      iapply (ownStepGhost_dyn γ dec _ h0 _ _ cv.ID' s).2
      rw [Hro]
      iframe Hgr
      ipureintro
      refine ⟨HD, ?_⟩
      rw [Hdiff]; rfl
    iapply HΦ $$ %«$r0_ptr» %interface.nil
    isplitl
    · iapply ownRawNode_intro γ «$r0_ptr» cv.ID'
        { delivered := [], unpersisted := [], steps := [], term := W64 0,
          storage := interface.ok si, mode := .dyn dec (cfgState (GMap.listToSet csm.Voters') ∅) h0 h1,
          cfg := cfgState (GMap.listToSet csm.Voters') ∅ }
        s _ [] _ _ _ [] Hwf (fun h => by cases h) rfl ?_
        Hdlen0 (by rw [Hun]) Hsn trivial
        (by rw [Ht, HT]) (by rw [Hsg]) (by rw [Hpv, HpvF]) (by rw [Hgh]) (by rw [Hgh])
        (uint_Z_nonneg _)
        $$ «$r0» Hphys Hghost Hsdr ss Hhp [] [] [] Hcomm []
      all_goals first
        | (rw [Hsd, Hents]; iapply storedRecs_nil)
        | iapply ownSlice_nil
        | iapply ownSliceCap_nil
        | iempintro
        | iapply pendList_nil
        | (simp only; rw [HAW, Hasync])
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial
