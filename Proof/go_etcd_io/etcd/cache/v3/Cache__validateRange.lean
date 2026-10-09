/-
Proof of `Spec/Cache__validateRange.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__validateRange
public import Spec.go_etcd_io.etcd.client.v3.GetPrefixRangeEnd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.validateRange.wp_proof
    (wp_GetPrefixRangeEnd : GetPrefixRangeEnd.spec (GF := GF) (hG := hG)) :
    Cache.validateRange.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap startSl endSl start end_ d1 d2
  wp_start as ⟨Hc, Hs, He⟩
  iNamed Hc
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, ⟨%eKR, #HeKR⟩⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ He
  wp_auto
  wp_apply wp_string_to_bytes cf.pfx as %ps ⟨Hps, -⟩
  wp_apply wp_GetPrefixRangeEnd
  wp_apply wp_string_to_bytes (prefixRangeEnd cf.pfx) as %pe ⟨Hpe, -⟩
  -- `isFromKey`: `len(endKey) == 1 && endKey[0] == 0`, as `decide (end_ = [W8 0])`
  wp_join (Q := fun v => iprop(⌜v = #(decide (end_ = [W8 0]))⌝ ∗ endSl ↦*{d2} end_ ∗
      endKey_ptr ↦ endSl)) with [He endKey]
  · have hl1 : end_.length = 1 := by rw [Hlen.1, Hif]; rfl
    obtain ⟨b, rfl⟩ : ∃ b, end_ = [b] := by
      match end_, hl1 with
      | [b], _ => exact ⟨b, rfl⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z endSl.len by
      rw [Hif]; decide))]
    wp_apply wp_load_slice_index endSl (sint.Z (W64 0)) [b] _ b (by decide) $$ [He] as He
    · iframe He; ipureintro; rfl
    iframe
    ipureintro
    simp
  · iframe
    ipureintro
    have : end_ ≠ [W8 0] := by intro h; subst h; apply Hif; simp at Hlen; word
    rw [decide_eq_false this]
  iintro ⟨%Hv, He, endKey⟩
  subst Hv
  wp_auto
  have hsk : endSl.len = W64 0 ↔ end_ = [] := by
    constructor
    · intro h; apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, h]; rfl
    · intro h; subst h; simp at Hlen; word
  wp_if_destruct
  · -- single key
    have he : end_ = [] := hsk.1 (of_decide_eq_true Hif.symm)
    wp_if_destruct
    · iapply HΦ
      iframe
      have hv : validRange cf.pfx start end_ = true := by unfold validRange; simp [he, Hif]
      simp only [rangeErr, hv, ↓reduceIte]
      ipureintro; trivial
    · have hp : cf.pfx ≠ [] := Hif
      wp_apply bytes.wp_Compare $$ [$Hs $Hps] as ⟨Hs, Hps⟩
      wp_if_destruct
      · iapply HΦ
        iframe
        have hlt : go.GoStringLt start cf.pfx := (compareResult_lt _ _).1 (by simpa using Hif)
        have hv : validRange cf.pfx start end_ = false := by unfold validRange; simp [he, hp, hlt]
        simp only [rangeErr, hv, ↓reduceIte, Bool.false_eq_true]
        iexact HeKR
      · have hlt : ¬ go.GoStringLt start cf.pfx := fun h => Hif (by simpa using (compareResult_lt _ _).2 h)
        wp_apply bytes.wp_Compare $$ [$Hs $Hpe] as ⟨Hs, Hpe⟩
        wp_if_destruct
        · iapply HΦ
          iframe
          have hge : ¬ go.GoStringLt start (prefixRangeEnd cf.pfx) :=
            (compareResult_ge _ _).1 (by simpa using Hif)
          have hv : validRange cf.pfx start end_ = false := by unfold validRange; simp [he, hp, hge]
          simp only [rangeErr, hv, ↓reduceIte, Bool.false_eq_true]
          iexact HeKR
        · iapply HΦ
          iframe
          have hge : go.GoStringLt start (prefixRangeEnd cf.pfx) :=
            Classical.byContradiction fun h => Hif (by simpa using (compareResult_ge _ _).2 h)
          have hv : validRange cf.pfx start end_ = true := by unfold validRange; simp [he, hlt, hge]
          simp only [rangeErr, hv, ↓reduceIte]
          ipureintro; trivial
  · have he : end_ ≠ [] := fun h => Hif (decide_eq_true (hsk.2 h)).symm
    wp_if_destruct
    · -- from key
      have h0 : end_ = [W8 0] := of_decide_eq_true Hif.symm
      wp_if_destruct
      · iapply HΦ
        iframe
        have hv : validRange cf.pfx start end_ = true := by unfold validRange; rw [ite_eq_right he, ite_eq_left h0]; simp [Hif]
        simp only [rangeErr, hv, ↓reduceIte]
        ipureintro; trivial
      · iapply HΦ
        iframe
        have hv : validRange cf.pfx start end_ = false := by unfold validRange; rw [ite_eq_right he, ite_eq_left h0]; simp [Hif]
        simp only [rangeErr, hv, ↓reduceIte, Bool.false_eq_true]
        iexact HeKR
    · have h0 : end_ ≠ [W8 0] := fun h => Hif (decide_eq_true h).symm
      wp_apply bytes.wp_Compare $$ [$He $Hs] as ⟨He, Hs⟩
      wp_if_destruct
      · iapply HΦ
        iframe
        have hle : ¬ go.GoStringLt start end_ := (compareResult_le _ _).1 (by simpa using Hif)
        have hv : validRange cf.pfx start end_ = false := by unfold validRange; rw [ite_eq_right he, ite_eq_right h0]; simp [hle]
        simp only [rangeErr, hv, ↓reduceIte, Bool.false_eq_true]
        iexact HeKR
      · have hlt : go.GoStringLt start end_ :=
          Classical.byContradiction fun h => Hif (by simpa using (compareResult_le _ _).2 h)
        wp_if_destruct
        · iapply HΦ
          iframe
          have hv : validRange cf.pfx start end_ = true := by unfold validRange; rw [ite_eq_right he, ite_eq_right h0]; simp [hlt, Hif]
          simp only [rangeErr, hv, ↓reduceIte]
          ipureintro; trivial
        · have hp : cf.pfx ≠ [] := Hif
          wp_apply bytes.wp_Compare $$ [$Hs $Hps] as ⟨Hs, Hps⟩
          wp_if_destruct
          · iapply HΦ
            iframe
            have hsp : go.GoStringLt start cf.pfx := (compareResult_lt _ _).1 (by simpa using Hif)
            have hv : validRange cf.pfx start end_ = false := by
              unfold validRange; rw [ite_eq_right he, ite_eq_right h0]; simp [hp, hsp]
            simp only [rangeErr, hv, ↓reduceIte, Bool.false_eq_true]
            iexact HeKR
          · have hsp : ¬ go.GoStringLt start cf.pfx :=
              fun h => Hif (by simpa using (compareResult_lt _ _).2 h)
            wp_apply bytes.wp_Compare $$ [$He $Hpe] as ⟨He, Hpe⟩
            wp_if_destruct
            · iapply HΦ
              iframe
              have hgt : go.GoStringLt (prefixRangeEnd cf.pfx) end_ :=
                (compareResult_gt _ _).1 (by simpa using Hif)
              have hv : validRange cf.pfx start end_ = false := by
                unfold validRange; rw [ite_eq_right he, ite_eq_right h0]; simp [hp, hgt]
              simp only [rangeErr, hv, ↓reduceIte, Bool.false_eq_true]
              iexact HeKR
            · iapply HΦ
              iframe
              have hgt : ¬ go.GoStringLt (prefixRangeEnd cf.pfx) end_ :=
                fun h => Hif (by simpa using (compareResult_gt _ _).2 h)
              have hv : validRange cf.pfx start end_ = true := by
                unfold validRange; rw [ite_eq_right he, ite_eq_right h0]; simp [hlt, hsp, hgt]
              simp only [rangeErr, hv, ↓reduceIte]
              ipureintro; trivial

end proof

end EtcdGrove
end Perennial
