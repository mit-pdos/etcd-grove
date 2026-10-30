module
public import Spec.go_etcd_io.bbolt.internal.freelist.NewHashMapFreelist
public import Spec.go_etcd_io.bbolt.internal.freelist.newShared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The empty `hashMap` is consistent. -/
theorem hashOK_empty : hashOK (W64 0) ∅ ∅ ∅ [] := by
  refine ⟨⟨fun st sz h => by simp at h, fun _ _ _ _ _ h => by simp at h⟩, ⟨List.Pairwise.nil,
    fun x => by simp⟩, ⟨fun k v => by simp, fun sz st => by simp, fun sz set h => by simp at h⟩,
    rfl, by simp⟩

theorem NewHashMapFreelist.wp_proof (hNS : newShared.spec (GF := GF) (hG := hG)) :
    NewHashMapFreelist.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply hNS as %s Hsh
  unfold ownShared ownSharedC
  icases Hsh with ⟨%sv, %c, Hsh, %Hok⟩
  iNamed Hsh
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %fm Hfm
  wp_apply (wp_map_make1 (K := w64) (V := w64)) as %fw Hfw
  wp_apply_core (wp_map_make1 (K := w64) (V := w64))
  iintro %bw Hbw
  wp_pures
  wp_alloc hp as Hhp
  iStructNamed Hhp
  ipersist shared
  wp_auto
  try isimp only at Hs
  ispecialize HΦ $$ %hp %s
  rw [show interface.mkOk (go.GoType.PointerType hashMap.ty) #hp = (hashMapImpl (GF := GF) hp).iface
    from rfl]
  iapply HΦ
  unfold ownFL; simp only [hashMapImpl]; unfold hashHdl ownHashMap ownHashPart hmRaw ownShared ownSharedC
  iframe shared
  isplitl [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
  · iexists _, c
    isplitl
    · iexists pp
      simp only [named]
      iframe
      ipureintro; rfl
    · ipureintro; exact Hok
  · isplitl []
    · iexact Hpkg
    isplitl
    · iexists _, ∅, ∅, ∅
      isplitl
      · iexists fm, fw, bw, ∅
        simp only [named]
        iframe
        iapply (BigSepM2.bigSepM2_empty _).2
        itrivial
      · ipureintro; exact hashOK_empty
    · ipureintro; simp [FLState.empty]

end proof

end bbolt
end EtcdGrove
end Perennial
