module
public import Spec.go_etcd_io.bbolt.Bucket__openBucket_w
public import Spec.go_etcd_io.bbolt.cloneBytes
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.openBucket.wp_wproof (hnewBucket : newBucket.spec (GF := GF) (hG := hG))
    (hclone : cloneBytes.spec (GF := GF) (hG := hG))
    (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Bucket.openBucket.wspec (GF := GF) (hG := hG) := by
  intro bl bv dqb dqw value v dv H16 Hinl
  wp_start as ⟨Hb, Hw, Hv⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hvl := ownSlice_len _ _ _ $$ Hv
  wp_auto
  wp_apply hnewBucket bv.tx' true dqw $$ [Hw] as %bm %nm ⟨Hw, Hmaps⟩
  · iframe
  try simp only [↓reduceIte]
  icases Hmaps with ⟨Hbm, Hnm⟩
  try wp_auto
  have Hne : v ≠ [] := by intro h; rw [h] at H16; simp at H16
  icases slice_car_keep value v dv Hne $$ Hv with ⟨%Hcar, Hv⟩
  have Hlen0 : 0 < sint.Z value.len := by
    have := Hvl.1; unfold sint.nat at this; word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, Hlen0⟩)]
  unfold sliceIndexRef
  rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero]
  try wp_auto
  by_cases Hal : ptrAddr value.ptr &&& W64 7 = W64 0
  · rw [decide_eq_true Hal]
    simp only [Bool.not_true]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, Hlen0⟩)]
    unfold sliceIndexRef
    rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero]
    icases (ownSlice_bytes value v dv Hne).1 $$ Hv with ⟨Hsb, %Hsl⟩
    icases (value_inbucket (hG := hG) value.ptr dv v H16 Hcar).1 $$ Hsb with ⟨Hib, Hrest⟩
    try wp_auto
    ihave Hsb := (value_inbucket (hG := hG) value.ptr dv v H16 Hcar).2 $$ [Hib Hrest]
    · iframe
    ihave Hv := (ownSlice_bytes value v dv Hne).2 $$ [Hsb]
    · iframe; ipureintro; exact Hsl
    wp_method_call
    try wp_auto
    wp_apply hRoot $$ [«$r0»] as Hnib
    · iframe
    by_cases Hr0 : inBucketRoot v = 0
    · rw [decide_eq_true ((ibOf_root_zero v).2 Hr0)]
      try wp_auto
      have H16l : 16 < sint.Z value.len := by have := Hinl Hr0; have := Hsl.1; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, H16l⟩)]
      unfold sliceIndexRef
      rw [arrayIndexRef_w8 (hG := hG) value.ptr _ Hcar]
      try wp_auto
      ispecialize HΦ $$ %child_ptr %«$r0_ptr» %(value.ptr +ₗ 16) %bm %nm
      iapply HΦ
      isimp only [newBucketOf, show sint.Z (W64 16) = (16 : Int) from rfl] at child
      unfold wOpenedOf; simp only [Hr0, ↓reduceIte]
      iframe
      ileft; ipureintro; trivial
    · rw [decide_eq_false (fun h => Hr0 ((ibOf_root_zero v).1 h))]
      try wp_auto
      ispecialize HΦ $$ %child_ptr %«$r0_ptr» %(value.ptr +ₗ 16) %bm %nm
      iapply HΦ
      isimp only [newBucketOf, show sint.Z (W64 16) = (16 : Int) from rfl] at child
      unfold wOpenedOf; simp only [Hr0, ↓reduceIte]
      iframe
      ileft; ipureintro; trivial
  · rw [decide_eq_false Hal]
    simp only [Bool.not_false]
    try wp_auto
    wp_apply hclone value v dv $$ [Hv] as %c ⟨Hc, Hcap, Hv⟩
    · iframe
    try wp_auto
    icases slice_car_keep c v (DFrac.own 1) Hne $$ Hc with ⟨%Hccar, Hc⟩
    ihave %Hcl := ownSlice_len _ _ _ $$ Hc
    have Hclen0 : 0 < sint.Z c.len := by
      have := Hcl.1; unfold sint.nat at this; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, Hclen0⟩)]
    unfold sliceIndexRef
    rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero]
    try wp_auto
    icases (ownSlice_bytes c v (DFrac.own 1) Hne).1 $$ Hc with ⟨Hsb, %Hsl⟩
    icases (value_inbucket (hG := hG) c.ptr (DFrac.own 1) v H16 Hccar).1 $$ Hsb with ⟨Hib, Hrest⟩
    wp_method_call
    try wp_auto
    wp_apply hRoot $$ [Hib] as Hib
    · iframe
    by_cases Hr0 : inBucketRoot v = 0
    · rw [decide_eq_true ((ibOf_root_zero v).2 Hr0)]
      try wp_auto
      have H16l : 16 < sint.Z c.len := by have := Hinl Hr0; have := Hsl.1; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, H16l⟩)]
      unfold sliceIndexRef
      rw [arrayIndexRef_w8 (hG := hG) c.ptr _ Hccar]
      try wp_auto
      ispecialize HΦ $$ %child_ptr %c.ptr %(c.ptr +ₗ 16) %bm %nm
      iapply HΦ
      isimp only [newBucketOf, show sint.Z (W64 16) = (16 : Int) from rfl] at child
      unfold wOpenedOf; simp only [Hr0, ↓reduceIte]
      iframe
      try (iright; iframe)
    · rw [decide_eq_false (fun h => Hr0 ((ibOf_root_zero v).1 h))]
      try wp_auto
      ispecialize HΦ $$ %child_ptr %c.ptr %(c.ptr +ₗ 16) %bm %nm
      iapply HΦ
      isimp only [newBucketOf, show sint.Z (W64 16) = (16 : Int) from rfl] at child
      unfold wOpenedOf; simp only [Hr0, ↓reduceIte]
      iframe
      try (iright; iframe)

end proof

end bbolt
end EtcdGrove
end Perennial
