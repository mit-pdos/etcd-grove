/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Trace__AddField.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__AddField
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

theorem traceutil.Trace.AddField.wp_proof
    (hUpd : traceutil.Trace.updateFieldIfExist.spec (GF := GF) (hG := hG)) :
    traceutil.Trace.AddField.spec (GF := GF) (hG := hG) := by
  intro t e fields fs dq
  wp_start as ⟨Ht, Hfs, %Hwf⟩
  ihave %Hfl := ownSlice_len $$ Hfs
  wp_auto
  ihave IH : iprop(∃ (n : w64) (x : traceutil.Field),
      "i" ∷ i_ptr ↦ n ∗ "f" ∷ f_ptr ↦ x ∗ "t" ∷ t_ptr ↦ t ∗ "Ht" ∷ traceutil.ownTrace t e ∗
      "Hfs" ∷ fields ↦*{dq} fs ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i f t Ht Hfs]
  · iexists W64 0, zero_val traceutil.Field
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < fs.length := by have h2 := Hfl.1; have h3 := Hn.1; rw [h2]; word
    obtain ⟨x0, Hx0⟩ : ∃ x0, fs[sint.nat n]? = some x0 := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z fields.len := ⟨Hn.1, Hif⟩
    rw [ite_eq_left Hbnd]
    wp_apply wp_load_slice_index fields (sint.Z n) fs dq x0 Hn.1 $$ [Hfs] as Hfs
    · iframe; ipureintro; exact Hx0
    (try wp_auto)
    have Hwf0 : traceutil.fieldsWf [x0] := traceutil.fieldsWf_of_mem Hwf (List.mem_of_getElem? Hx0)
    wp_apply hUpd t e x0 $$ [Ht] as %b Ht
    · iframe #; iframe Ht; ipureintro; exact Hwf0
    cases b
    · (try wp_auto)
      iunfold traceutil.ownTrace at Ht
      icases Ht with ⟨%v, %ss, Ht, Hfs0, Hss, Hcap, Hsf, %He⟩
      iunfold traceutil.ownFields at Hfs0
      icases Hfs0 with ⟨%ffs, Hffs, Hfcap, %Hfwf⟩
      (try wp_auto)
      wp_apply wp_slice_literal (V := traceutil.Field) [x0]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      (try wp_auto)
      wp_apply wp_slice_append (V := traceutil.Field) _ _ _ _ _ $$ [$Hffs $Hfcap $Hsl2]
        as %sl3 ⟨Hffs, Hfcap, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, x0
      simp only [named]
      iframe
      isplitl
      · ihave Hfs0 : traceutil.ownFields sl3 $$ [Hffs Hfcap]
        · iunfold traceutil.ownFields
          iexists _
          iframe
          ipureintro
          exact traceutil.fieldsWf_append Hfwf Hwf0
        iunfold traceutil.ownTrace
        iexists _, _
        iframe Ht
        (try simp only)
        iframe
        ipureintro; exact He
      ipureintro; constructor <;> word
    · (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, x0
      simp only [named]
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
