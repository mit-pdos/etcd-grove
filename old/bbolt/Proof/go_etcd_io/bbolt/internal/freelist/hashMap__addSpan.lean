module
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__addSpan

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

theorem hashMap.addSpan.wp_proof : hashMap.addSpan.spec (GF := GF) (hG := hG) := by
  intro h cnt sp bwm sets start size
  wp_start as Hraw
  unfold hmRaw
  iNamed Hraw
  ihave %Hdom := BigSepM2.bigSepM2_lookup_iff $$ Hsets
  wp_auto
  wp_apply wp_mapInsert $$ [Hbw] as Hbw
  · iexact Hbw
  try wp_auto
  wp_apply wp_mapInsert $$ [Hfw] as Hfw
  · iexact Hfw
  try wp_auto
  wp_apply wp_map_lookup2 $$ [Hfm] as Hfm
  · iexact Hfm
  try wp_auto
  wp_join iprop(∃ (FM' : GMap w64 Loc) (l : Loc), fm ↦$ FM' ∗
      ([∗map] _sz ↦ l;st ∈ FM';<[size := (sets !! size).getD ∅]> sets, l ↦$ st) ∗
      ⌜FM' !! size = some l⌝ ∗ structFieldRef hashMap go!"freemaps" h ↦ fm ∗ f_ptr ↦ h ∗
      size_ptr ↦ size)
    with [Hfm Hsets Hfmf f size] as ⟨%FM', %l, Hfm, Hsets, %HFl, Hfmf, f, size⟩
  · -- the set of this size exists
    obtain ⟨l0, hl0⟩ := Option.isSome_iff_exists.1 (show (FM !! size).isSome = true by
      cases h : FM !! size with
      | none => rw [h] at Hif; simp at Hif
      | some _ => rfl)
    obtain ⟨st0, hst0'⟩ := Option.isSome_iff_exists.1
      ((Hdom size).1 (by simp only [show Std.get? FM size = some l0 from hl0, Option.isSome_some]))
    have hst0 : sets !! size = some st0 := hst0'
    iexists FM, l0
    rw [hst0, Option.getD_some, GMap.insert_id sets size st0 hst0]
    iframe
    ipureintro; exact hl0
  · -- no set of this size yet: a new one
    have hn : FM !! size = none := by
      cases h : FM !! size
      · rfl
      · simp [h] at Hif
    have hs : sets !! size = none := by
      have := Hdom size
      simp only [show Std.get? FM size = FM !! size from rfl, hn, Option.isSome_none] at this
      cases h : sets !! size
      · rfl
      · simp [show Std.get? sets size = sets !! size from rfl, h] at this
    try wp_auto
    wp_apply (wp_map_make1 (K := w64) (V := Unit)) as %m0 Hm0
    try wp_auto
    wp_apply wp_mapInsert $$ [Hfm] as Hfm
    · iexact Hfm
    wp_join_done
    iexists (<[size := m0]> FM), m0
    iframe
    rw [hs]
    isplitl [Hsets Hm0]
    · iapply (BigSepM2.bigSepM2_insert (show Std.get? FM size = none from hn)
        (show Std.get? sets size = none from hs)).2
      iframe
    ipureintro; exact GMap.lookup_insert _ _ _
  try wp_auto
  have hst : (<[size := (sets !! size).getD ∅]> sets) !! size = some ((sets !! size).getD ∅) :=
    GMap.lookup_insert _ _ _
  icases BigSepM2.bigSepM2_insert_acc (show Std.get? FM' size = some l from HFl) hst $$ Hsets
    with ⟨Hl, Hback⟩
  wp_apply wp_map_lookup1 $$ [Hfm] as Hfm
  · iexact Hfm
  rw [HFl, Option.getD_some]
  try wp_auto
  wp_apply wp_mapInsert $$ [Hl] as Hl
  · iexact Hl
  try wp_auto
  ihave Hsets := Hback $$ %l %(<[start := ()]> ((sets !! size).getD ∅)) Hl
  try wp_auto
  rw [show (Std.insert FM' size l : GMap w64 Loc) = FM' from GMap.insert_id FM' size l HFl,
    show (Std.insert (<[size := (sets !! size).getD ∅]> sets) size (<[start := ()]> ((sets !! size).getD ∅)) :
      GMap w64 (GMap w64 Unit)) = <[size := <[start := ()]> ((sets !! size).getD ∅)]> sets from
      GMap.insert_insert _ _ _ _]
  iapply HΦ
  iexists fm, fw, bw, FM'
  simp only [named]
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
