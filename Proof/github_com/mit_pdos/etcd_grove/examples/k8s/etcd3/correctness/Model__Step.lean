/-
Lean-first (no Rocq counterpart).

The proof of `(*Model).Step`: `IsTooManyRequests` is false on the output's (flat) error; then
`execute`, and by the request's kind `validateGet`, `validateList` or the responses' `DeepEqual`
(the write's clone frozen).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__Step
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__execute
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__validateGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__validateList
public import Spec.k8s_io.apimachinery.pkg.api.errors.IsTooManyRequests

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]
variable [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]
variable [apierrors_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem Model.Step.wp_proof
    (wp_DE : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG))
    (wp_exec : Model.execute.spec (GF := GF) (hG := hG))
    (wp_VG : Model.validateGet.spec (GF := GF) (hG := hG))
    (wp_VL : Model.validateList.spec (GF := GF) (hG := hG))
    (wp_TMR : apierrors.IsTooManyRequests.spec (GF := GF) (hG := hG))
    (wp_Unwrap : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG)) :
    Model.Step.spec (GF := GF) (hG := hG) := by
  intro mp m x r ro out hfit hin hparse hlist hnoth hfo hlo hoo hsz
  cases ro with | mk o2 e2 =>
  cases out with | mk oo oe =>
  simp only at hfo hlo hoo
  wp_start as ⟨#Hm, #Hr, #Hro⟩
  ihave #Hro0 := Hro
  iunfold respRep at Hro
  icases Hro with ⟨#Ho2, #He2⟩
  ihave %hm2 := deepRep_nil_iff _ _ _ $$ Ho2
  wp_auto
  wp_join (v := #false) at (if: _ then _ else #false) with [output]
  · cases o2 with
    | ok io => wp_auto; wp_join_done
    | nil =>
      wp_auto
      wp_apply (wp_TMR _) $$ [] as %b #Hq
      · iright
        iapply errRep_apiErrOk wp_Unwrap _ oe hfo $$ He2
      ihave %hb : ⌜b = false⌝ $$ []
      · iapply errRep_notTooMany wp_Unwrap _ oe hfo b
        iframe He2 Hq
      subst hb
      wp_join_done
  have hlx : x.Kind' = W64 4 → (parseRVD x.MinRV').isSome ∧ 0 ≤ sint.Z x.Limit' ∧
      (0 < sint.Z x.Limit' → x.MinRV' ≠ go!"0") := fun h => ⟨hparse, (hlist h).1, (hlist h).2⟩
  wp_apply (wp_exec mp m x r hfit hin hlx hsz) $$ [] as %resp %np %cp ⟨#Hresp, #Hcp, Hnp⟩
  · iframe Hm Hr
  cases resp with | mk o1 e1 =>
  by_cases k4 : x.Kind' = W64 4
  · iunfold reqRep at Hr
    isimp only [k4, ↓reduceIte] at Hr
    icases Hr with %Hr
    obtain ⟨hop, hkey, hopts⟩ := Hr
    have hw : isWriteL x = false := by simp [isWriteL, k4]
    rw [hw]
    isimp only [Bool.false_eq_true, ↓reduceIte] at Hnp
    icases Hnp with %Hnp
    obtain ⟨hnp, hm'⟩ := Hnp
    subst np
    rw [hop, decide_eq_false (by simp)]
    wp_auto
    rw [hkey, hopts]
    have hle : listOrNilD (rexecL x m).1.obj := by
      unfold rexecL; rw [if_pos k4]; exact rlistL_listOrNil x m
    wp_apply (wp_VL mp m x _ _ (rexecL x m).1 ⟨oo, oe⟩ hparse (rexecL_flat x m hnoth) hfo hle
      (hlo k4)) $$ []
    · iframe Hm Hresp Hro0
    have hst : rstepL x m ⟨oo, oe⟩ = (rvalidateListL x m (rexecL x m).1 ⟨oo, oe⟩, m, none) := by
      unfold rstepL; rw [if_pos k4]
    rw [hst]
    iapply HΦ
    iframe Hm
    unfold changeRep
    ipureintro; exact ⟨rfl, rfl⟩
  by_cases hwr : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2
  · ihave %hop : ⌜r.Op' ≠ go!"Get" ∧ r.Op' ≠ go!"List"⌝ $$ [Hr]
    · iunfold reqRep at Hr
      rcases hwr with h | h | h
      · isimp [h] at Hr
        icases Hr with ⟨%Hr, -⟩
        ipureintro; rw [Hr.1]; simp
      · isimp [h] at Hr
        icases Hr with ⟨%Hr, -⟩
        ipureintro; rw [Hr.1]; simp
      · isimp [h] at Hr
        icases Hr with ⟨%Hr, -⟩
        ipureintro; rw [Hr.1]; simp
    have hw : isWriteL x = true := by
      rcases hwr with h | h | h <;> simp [isWriteL, h]
    rw [hw]
    isimp only [↓reduceIte] at Hnp
    rw [decide_eq_false hop.1]
    wp_auto
    rw [decide_eq_false hop.2]
    wp_auto
    ihave #Hresp' := Hresp
    iunfold respRep at Hresp'
    icases Hresp' with ⟨#Ho1, #He1⟩
    wp_apply (wp_DeepEqual_resp wp_DE _ _ _ _ (rexecL x m).1.obj oo (rexecL x m).1.err oe
      (rexecL_write_deep x m hwr hnoth) hfo) $$ []
    · iframe Ho1 He1 Ho2 He2
    have hst : rstepL x m ⟨oo, oe⟩ =
        if respEqL (rexecL x m).1 ⟨oo, oe⟩ then (true, (rexecL x m).2.1, (rexecL x m).2.2)
        else (false, m, none) := by
      unfold rstepL; rw [if_neg k4, if_pos hwr]
    rw [hst]
    cases hb : respEqL ⟨(rexecL x m).1.obj, (rexecL x m).1.err⟩ ⟨oo, oe⟩
    · wp_auto
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hm
      unfold changeRep
      ipureintro; trivial
    · iapply wp_fupd
      wp_auto
      imod modelOwn_freeze _ _ $$ Hnp with #Hnp
      imodintro
      iapply HΦ
      simp only [↓reduceIte]
      iframe Hnp Hcp
  simp only [not_or] at hwr
  obtain ⟨k0, k1, k2⟩ := hwr
  iunfold reqRep at Hr
  isimp only [k4, k0, k1, k2, ↓reduceIte] at Hr
  icases Hr with %Hr
  obtain ⟨hop, hkey, hrv, hinf⟩ := Hr
  have hw : isWriteL x = false := by
    simp only [isWriteL, decide_eq_false k0, decide_eq_false k1, decide_eq_false k2]; rfl
  rw [hw]
  isimp only [Bool.false_eq_true, ↓reduceIte] at Hnp
  icases Hnp with %Hnp
  obtain ⟨hnp, hm'⟩ := Hnp
  subst np
  rw [hop, decide_eq_true rfl]
  wp_auto
  wp_apply (wp_VG mp m x _ _ _ (rexecL x m).1 ⟨oo, oe⟩ hrv hparse (rexecL_flat x m hnoth) hfo
    (hoo hw k4)) $$ []
  · iframe Hm Hresp Hro0
  have hst : rstepL x m ⟨oo, oe⟩ = (rvalidateGetL x m (rexecL x m).1 ⟨oo, oe⟩, m, none) := by
    unfold rstepL; rw [if_neg k4, if_neg (by rintro (h | h | h) <;> contradiction)]
  rw [hst]
  iapply HΦ
  iframe Hm
  unfold changeRep
  ipureintro; exact ⟨rfl, rfl⟩

end proof

end k8s_correctness
end EtcdGrove
end Perennial
