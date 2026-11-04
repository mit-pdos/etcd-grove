/-
`NewHashMapFreelist()` (U2 internal): a fresh, empty hash map freelist with no reader.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.newShared
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Open

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

abbrev NewHashMapFreelist.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist }}
    (App (Val #(functions go_etcd_io.bbolt.internal.freelist.NewHashMapFreelist [])) (Val #()))
  {{ (fli : GoInterface), RET #fli; ⌜fli ≠ interface.nil⌝ ∗ flPgOwn fli FLPg.empty ∗
      flRoOwn fli [] }}

/-- The empty `hashMap` is consistent. -/
theorem hashOK_empty : hashOK (W64 0) ∅ ∅ ∅ [] := by
  refine ⟨⟨fun st sz h => by simp at h, fun _ _ _ _ _ h => by simp at h⟩, ⟨List.Pairwise.nil,
    fun x => by simp⟩, ⟨fun k v => by simp, fun sz st => by simp, fun sz set h => by simp at h⟩,
    rfl, by simp⟩

theorem NewHashMapFreelist.wp_proof : NewHashMapFreelist.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply newShared.wp_proof as %s ⟨Hsh, Hro⟩
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  iunfold ownShC at Hsh
  icases Hsh with ⟨%al, %ca, %pe, %pp, Hsh⟩
  iNamed Hsh
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %fm Hfm
  wp_apply (wp_map_make1 (K := w64) (V := w64)) as %fw Hfw
  wp_apply +noauto (wp_map_make1 (K := w64) (V := w64)) as %bw Hbw
  wp_pures
  wp_alloc hp as Hhp
  iStructNamed Hhp
  ipersist shared
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; simp [interface.mkOk]
  isplitl [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds freePagesCount freemaps forwardMap
    backwardMap Hfm Hfw Hbw]
  · iapply (flPgOwn_close (hashImpl hp) hp s (interface.mkOk (go.GoType.PointerType hashMap.ty) #hp)
      FLPg.empty (Or.inr rfl) rfl)
    isplitl []
    · iExactEq shared; rfl
    isplitr [Hif Hal Hallocs Hca Hcache Hpe Hpending Hpds]
    · dsimp only [hashImpl]
      iexists W64 0, ∅, ∅, ∅, fm, fw, bw, ∅
      iframe
      isplitl []
      · iapply (BigSepM2.bigSepM2_empty _).2; itrivial
      ipureintro; exact hashOK_empty
    · iunfold ownSh
      iexists c
      isplitl
      · iunfold ownShC
        iexists al, ca, pe, pp
        iframe
      · ipureintro; exact Hok
  · iunfold flRoOwn
    iexists hp, s, slice.nil
    iframe
    isplitl []
    · iunfold flImplAt; iright; iframe shared; ipureintro; rfl
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
