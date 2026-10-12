module
public import Spec.go_etcd_io.bbolt.Bucket__Get
public import Spec.go_etcd_io.bbolt.Bucket__Cursor
public import Spec.go_etcd_io.bbolt.Cursor__seek

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

theorem Bucket.Get.wp_proof (hCursor : Bucket.Cursor.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek.spec (GF := GF) (hG := hG)) :
    Bucket.Get.spec (GF := GF) (hG := hG) := by
  intro bl V q key kb dk
  wp_start as ⟨HR, Hst, Hk⟩
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  icases bktR_acc _ _ _ $$ HR with ⟨%Hok, Hctx, Hpgs, HRback⟩
  wp_auto
  wp_apply hCursor bl V q $$ [Hctx Hpgs Hst] as %cl ⟨Hc, Hst⟩
  · iframe
  wp_apply hseek cl bl V q [] key kb dk Hok.1 (treeOK_wfAt V Hok.2) $$ [Hc Hk]
    as %es %r %pg ⟨%Hs, Hc, Hk⟩
  · iframe
  obtain ⟨Hlt, Hseek⟩ := Hs
  obtain ⟨pid, pre, Hes, -, -, Hpa, Hn, Hlen, Hfl, Hlw, Hli, Hcar⟩ := leafTop_facts V es r pg Hok.1 Hlt
  icases curI_drop _ _ _ _ _ $$ Hc with ⟨Hctx, Hpgs⟩
  ihave HR := HRback $$ Hctx Hpgs
  try wp_auto
  by_cases Hin : sint.Z r.index' < pageCount pg
  · have H0 : 0 ≤ sint.Z r.index' := Hseek.1
    rw [kv_inside r.page' pg _ H0 Hin]
    simp only
    obtain ⟨i, Hi⟩ : ∃ i : Nat, (i : Int) = sint.Z r.index' := ⟨_, Int.toNat_of_nonneg H0⟩
    have Hit : (sint.Z r.index').toNat = i := by omega
    rw [Hit]
    have Hic : i < pageCount pg := by omega
    by_cases Hf : W32 (leafFlags pg i) &&& W32 1 = W32 0
    · rw [decide_eq_true Hf]
      try wp_auto
      icases bktR_acc _ _ _ $$ HR with ⟨-, Hctx, Hpgs, HRback⟩
      icases bktPages_acc V q pid _ pg Hok.1 Hpa $$ Hpgs with ⟨Hpg, Hpgsback⟩
      icases leaf_key_acc _ _ pg i Hlw Hic Hcar $$ Hpg with ⟨Hks, Hkback⟩
      wp_apply bytes.wp_Equal key _ dk (DFrac.own q) kb (leafKey pg i) $$ [Hk Hks] as ⟨Hk, Hks⟩
      · iframe
      ihave Hpg := Hkback $$ Hks
      ihave Hpgs := Hpgsback $$ Hpg
      ihave HR := HRback $$ Hctx Hpgs
      by_cases Heq : kb = leafKey pg i
      · rw [decide_eq_true Heq]
        try wp_auto
        iapply HΦ
        iframe
        ipureintro; exact ⟨es, r, pg, Hlt, Hseek, Or.inr ⟨i, Hi, Hic, Heq.symm, Hf, rfl⟩⟩
      · rw [decide_eq_false Heq]
        try wp_auto
        iapply HΦ
        iframe
        ipureintro; exact ⟨es, r, pg, Hlt, Hseek, Or.inl rfl⟩
    · rw [decide_eq_false Hf]
      try wp_auto
      iapply HΦ
      iframe
      ipureintro; exact ⟨es, r, pg, Hlt, Hseek, Or.inl rfl⟩
  · rw [kv_past r.page' pg _ (by omega)]
    simp only
    rw [decide_eq_true (show W32 0 &&& W32 1 = W32 0 by decide)]
    try wp_auto
    ihave Hnil : slice.nil ↦* ([] : List w8) $$ []
    · iapply ownSlice_nil
    wp_apply bytes.wp_Equal key _ dk (DFrac.own 1) kb [] $$ [Hk Hnil] as ⟨Hk, -⟩
    · iframe
    by_cases Heq : kb = []
    · rw [decide_eq_true Heq]
      try wp_auto
      iapply HΦ
      iframe
      ipureintro; exact ⟨es, r, pg, Hlt, Hseek, Or.inl rfl⟩
    · rw [decide_eq_false Heq]
      try wp_auto
      iapply HΦ
      iframe
      ipureintro; exact ⟨es, r, pg, Hlt, Hseek, Or.inl rfl⟩

end proof

end bbolt
end EtcdGrove
end Perennial
