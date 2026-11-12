/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__updateFieldIfExist.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__updateFieldIfExist

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

theorem traceutil.Trace.updateFieldIfExist.wp_proof :
    traceutil.Trace.updateFieldIfExist.spec (GF := GF) (hG := hG) := by
  intro t e f
  wp_start as ⟨Ht, %Hwf⟩
  iunfold traceutil.ownTrace at Ht
  icases Ht with ⟨%v, %ss, Ht, Hfs, Hss, Hcap, Hsf, %He⟩
  iunfold traceutil.ownFields at Hfs
  icases Hfs with ⟨%ffs, Hffs, Hfcap, %Hfwf⟩
  ihave %Hfl := ownSlice_len $$ Hffs
  wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ (zero_val w64 : w64) : IProp GF) => gi
  ihave IH : iprop(∃ (n gn : w64) (x : traceutil.Field) (ffs' : List traceutil.Field),
      "i" ∷ i_ptr ↦ n ∗ "gi" ∷ gi_ptr ↦ gn ∗ "v" ∷ v_ptr ↦ x ∗ "t" ∷ t_ptr ↦ t ∗
      "f" ∷ f_ptr ↦ f ∗ "Ht" ∷ t ↦ v ∗ "Hffs" ∷ v.fields' ↦* ffs' ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ffs.length : Int) ∧ ffs'.length = ffs.length ∧
        traceutil.fieldsWf ffs'⌝) $$ [i gi v t f Ht Hffs]
  · iexists W64 0, zero_val w64, zero_val traceutil.Field, ffs
    simp only [named]
    iframe
    ipureintro; exact ⟨by word, by word, by simp, Hfwf⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ffs'.length := by
      have h1 := Hn.2.2.1; have h2 := Hfl.1; have h3 := Hn.1; rw [h1, h2]; word
    obtain ⟨x0, Hx0⟩ : ∃ x0, ffs'[sint.nat n]? = some x0 := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z v.fields'.len := ⟨Hn.1, Hif⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index v.fields' (sint.Z n) ffs' (DFrac.own 1) x0 Hn.1 $$ [Hffs] as Hffs
    · iframe; ipureintro; exact Hx0
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z n) x0 v.fields' _ ffs' Hn.1 Hx0 $$ Hffs with ⟨Hel, Hback⟩
      (try wp_auto)
      ihave Hffs := Hback $$ %_ Hel
      wp_for_post
      iapply HΦ
      ihave Hfs : traceutil.ownFields v.fields' $$ [Hffs Hfcap]
      · iunfold traceutil.ownFields
        iexists _
        iframe
        ipureintro
        exact traceutil.fieldsWf_set _ Hn.2.2.2 Hwf
      iunfold traceutil.ownTrace
      iexists _, _
      (try simp only)
      iframe
      ipureintro; exact He
    · (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n, x0, ffs'
      simp only [named]
      iframe
      ipureintro; exact ⟨by word, by word, Hn.2.2.1, Hn.2.2.2⟩
  · (try wp_auto)
    iapply HΦ
    ihave Hfs : traceutil.ownFields v.fields' $$ [Hffs Hfcap]
    · iunfold traceutil.ownFields
      iexists ffs'
      iframe
      ipureintro; exact Hn.2.2.2
    iunfold traceutil.ownTrace
    iexists _, _
    (try simp only)
    iframe
    ipureintro; exact He

end proof

end EtcdGrove
end Perennial
