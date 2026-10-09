/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Spec.go_etcd_io.raft.v3.raft__softState
public import Spec.go_etcd_io.raft.v3.raft__hardState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- `newRaft` on the empty storage is the protocol's initial state (`newRaft_post_init`);
the new `RawNode` holds it with nothing handed out. -/
theorem NewRawNode.wp_proof
    (wp_newRaft : newRaft.spec (GF := GF) (hG := hG))
    (wp_softState : raft.softState.spec (GF := GF) (hG := hG))
    (wp_hardState : raft.hardState.spec (GF := GF) (hG := hG)) :
    NewRawNode.spec (GF := GF) (hG := hG) := by
  intro γ c cv lok si σ hs cs voters dqv Hvalid Hlok Hsto Hmi Hcq Hdpf Hmcs Hasync Happ
    Hprev Hents Hss Hhs Hvne Hvnd Hv0 Hvlen Hc1 Hc2 Hc3 Hal Hcfg Hid
  wp_start as ⟨Hc, #Hlg, #Hst, HSt, #Hinit, Hghost, #Hcomm⟩
  wp_auto
  wp_apply wp_newRaft c cv lok si σ hs cs voters dqv Hvalid Hlok Hsto Hmi Hcq Hdpf Hmcs
    (by rw [Hents]; intro k e h; simp at h)
    (by rw [Hents]; intro e h; simp at h) Hss (fun h => absurd Hhs h) (.inl Happ)
    Hvne Hvnd Hv0 Hvlen Hc1 Hc2 Hc3 Hal
    $$ [$Hc $Hlg $Hst $HSt $Hinit] as %r %s %cv' ⟨Hphys, Hc, %HAW, %Hpost⟩
  try wp_auto
  wp_apply wp_softState _ r cv.ID' s $$ Hphys as Hphys
  -- `prevSoftSt` points to a `SoftState` nobody writes again
  ipersist ss
  wp_apply wp_hardState _ r cv.ID' s $$ Hphys as Hphys
  obtain ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho, -, Hp, Hse, Hue, Hcm, Hap, Hun, Hsn⟩ := Hpost
  have HT : hs.Term' = W64 0 := Hhs.1
  have Hrel : NStateRel s initPState :=
    newRaft_post_init hs s Hhs ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho⟩ (by rw [Hp, Hprev])
      (by rw [Hse, Hents]) Hue (by rw [Hcm]; simp [committedAfter, Hhs, Hprev])
  -- the ghost state's configuration is the node's
  ihave Hphys : ownRaftPhys γ.reCfg r cv.ID' s $$ [Hphys]
  · rw [Hcfg]; iexact Hphys
  iapply HΦ $$ %«$r0_ptr» %interface.nil
  isplitl
  · iapply ownRawNode_intro γ «$r0_ptr» cv.ID'
      { delivered := [], unpersisted := [], steps := [], advanceable := true, term := W64 0 }
      s initPState _ _ [] Hrel
      (by rw [Hcfg]; exact (GMap.elem_of_list_to_set _ _).2 Hid) ?_
      (by rw [Hap, Hprev, Happ]; rfl) (by rw [Hun]) Hsn (fun _ => by simp [StepsOk])
      (by rw [Ht, HT])
      $$ «$r0» Hphys Hghost ss [] [] [] [] Hcomm
    all_goals first
      | iapply ownSlice_nil
      | iapply ownSliceCap_nil
      | iempintro
      | (simp only; rw [HAW, Hasync])
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
