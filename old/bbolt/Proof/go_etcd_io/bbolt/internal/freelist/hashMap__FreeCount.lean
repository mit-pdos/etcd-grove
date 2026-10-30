module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__FreeCount
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__hashmapFreeCountSlow
public import Spec.go_etcd_io.bbolt.internal.common.Verify

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

/-- The count of a consistent `hashMap` is the number of free ids. -/
theorem fc_cnt {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) : cnt = W64 (free.length : Int) := by
  have := h.2.2.2.1; have := h.2.2.2.2; word

theorem hashMap.FreeCount.wp_proof (hVerify : Verify.spec (GF := GF) (hG := hG))
    (hSlow : hashMap.hashmapFreeCountSlow.spec (GF := GF) (hG := hG)) :
    hashMap.FreeCount.spec (GF := GF) (hG := hG) := by
  intro h s free
  wp_start as Hown
  unfold ownHashMap
  icases Hown with ⟨#Hpkg, Hpart, %Hge⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply (hVerify _ iprop(f_ptr ↦ h ∗ ownHashPart h s free)) $$ [f Hpart]
  · isplit
    · wp_auto
      wp_apply (hSlow h s free) $$ [Hpart] as Hpart
      · iexact Hpart
      unfold ownHashPart
      iNamed Hpart
      unfold hmRaw
      iNamed Hraw
      wp_auto
      rw [← fc_cnt Hok]
      wp_auto
      iframe
      iexists cnt, sp, bwm, sets
      simp only [named]
      iframe
      ipureintro; exact Hok
    · iframe
  iintro ⟨f, Hpart⟩
  unfold ownHashPart
  iNamed Hpart
  unfold hmRaw
  iNamed Hraw
  wp_auto
  rw [← fc_cnt Hok]
  iapply HΦ
  iframe Hpkg
  isplitl
  · iexists cnt, sp, bwm, sets
    simp only [named]
    iframe
    ipureintro; exact Hok
  ipureintro; exact Hge

end proof

end bbolt
end EtcdGrove
end Perennial
