/-
`value.MapZipUsing`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.MapZipUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__ZipUsing
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem value.MapZipUsing.wp_proof
    (h_mapUnstructuredString_ZipUsing : value.mapUnstructuredString.ZipUsing.spec (GF := GF)) :
    value.MapZipUsing.spec (GF := GF) := fun al lm rm ol or_ order fn I Q => by
  wp_start as ⟨Ha, Hl, Hr, %Hord, %Hzl, #Hfn, HI⟩
  ihave %Hlc := isMapO_cases $$ Hl
  ihave %Hrc := isMapO_cases $$ Hr
  wp_auto
  rcases Hlc with ⟨rfl, rfl⟩ | ⟨kvs, gm, rfl, rfl⟩
  · rcases Hrc with ⟨rfl, rfl⟩ | ⟨kvs, gm, rfl, rfl⟩
    · wp_auto
      iapply HΦ
      iframe
      rw [ValuePure.zipKeys_none_none]
      simp only [mapIterPost, ↓reduceIte]
      iexists []
      iframe
      ipureintro
      simp [mapIterDone]
    · wp_auto
      ipersist fn
      wp_func_lits
      wp_apply h_mapUnstructuredString_ZipUsing gm kvs al _ none order _ I Q $$ [Hr Ha HI] as %b ⟨Ha, Hb⟩
      · iframe
        isplitl [Hr]
        · simp only [isMapO]; iexact Hr
        isplitr
        · simp only [isMapO]; ipureintro; trivial
        isplitr
        · ipureintro; exact Hord
        isplitr
        · ipureintro; intro h; have := Hzl h; simp only [kvsOrEmpty, Option.getD] at this ⊢; omega
        iunfold zipFnOk
        imodintro
        iintro %done %k %vl %vr %Hstep %Φ' !> ⟨Ha, HI, Hvl, Hvr⟩ HΦ'
        rw [ValuePure.zipKeys_swap_none] at Hstep
        rw [← recv_eq_func_mk]
        wp_call
        wp_auto
        iunfold zipFnOk at Hfn
        wp_apply Hfn $$ %done %k %vr %vl %Hstep [Ha HI Hvr Hvl] as %b ⟨Ha, Hvr, Hvl, Hb⟩
        · iframe
        iapply HΦ'
        iframe
      iapply HΦ
      iframe
      rw [← ValuePure.zipKeys_swap_none]
      iexact Hb
  · wp_auto
    wp_apply h_mapUnstructuredString_ZipUsing gm kvs al rm or_ order fn I Q $$ [Hl Hr Ha HI] as %b Hb
    · iframe
      isplitl [Hl]
      · simp only [isMapO]; iexact Hl
      isplitr
      · ipureintro; exact Hord
      isplitr
      · ipureintro; exact Hzl
      iexact Hfn
    wp_end

end proof

end smd
end EtcdGrove
end Perennial
