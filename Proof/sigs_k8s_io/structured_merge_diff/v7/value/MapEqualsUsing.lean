/-
`value.MapEqualsUsing`: proved (the unordered zip: every key's two sides equal). Its callees'
specs (and the interface bundles' laws, `Objects.lean`) are its hypotheses.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.MapEqualsUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.MapZipUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsing
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsCmp

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

theorem value.MapEqualsUsing.wp_proof
    (wp_MapZipUsing : value.MapZipUsing.spec (GF := GF))
    (wp_EqualsUsing : value.EqualsUsing.spec (GF := GF))
    (h_mapM : isMapV_methods.law (GF := GF)) :
    value.MapEqualsUsing.spec (GF := GF) := fun al lm rm ol or_ => by
  wp_start as ⟨Ha, #Hl, #Hr⟩
  ihave %Hlc := isMapO_cases lm ol $$ Hl
  ihave %Hrc := isMapO_cases rm or_ $$ Hr
  rcases Hlc with ⟨rfl, rfl⟩ | ⟨l, gl, rfl, rfl⟩ <;> rcases Hrc with ⟨rfl, rfl⟩ | ⟨r, gr, rfl, rfl⟩
  · wp_auto
    iapply HΦ; iframe; ipureintro; simp
  · wp_auto
    iapply HΦ; iframe; ipureintro; simp
  · wp_auto
    iapply HΦ; iframe; ipureintro; simp
  · simp only [isMapO] at *
    ihave %hsl := isMapV_sorted_law_holds _ l $$ Hl
    ihave %hsr := isMapV_sorted_law_holds _ r $$ Hr
    ihave ⟨-, %il, %hil, #HML⟩ := h_mapM (interface.mkOk value.mapUnstructuredString.ty #gl) l $$ [Hl]
    · isplitr; iexact Hpkg; iexact Hl
    ihave ⟨-, %ir, %hir, #HMR⟩ := h_mapM (interface.mkOk value.mapUnstructuredString.ty #gr) r $$ [Hr]
    · isplitr; iexact Hpkg; iexact Hr
    simp only [interface.mkOk, GoInterface.ok.injEq] at hil hir
    subst hil hir
    iunfold mapIfaceM at HML HMR
    icases HML with ⟨#HLL, -⟩
    icases HMR with ⟨#HLR, -⟩
    wp_auto
    wp_apply HLL $$ %l as %nl %Hnl
    · iexact Hl
    try wp_auto
    wp_apply HLR $$ %r as %nr %Hnr
    · iexact Hr
    try wp_auto
    by_cases hn : nl = nr
    · rw [decide_eq_true hn]
      wp_auto
      ipersist a
      wp_func_lits
      wp_apply wp_MapZipUsing al _ _ (some l) (some r) (W64 0) _
        (fun done => iprop(⌜∀ k ∈ done, lookupKV k l = lookupKV k r⌝)) (iprop(⌜l ≠ r⌝))
        $$ [Ha] as %b ⟨Ha, Hpost⟩
      · iframe
        simp only [isMapO]
        isplitr; iexact Hl
        isplitr; iexact Hr
        isplitr; ipureintro; left; rfl
        isplitr; ipureintro; intro h; exact absurd h (by decide)
        isplitr
        · iunfold zipFnOk
          imodintro
          iintro %done %k %vl %vr %Hst %Φ' !> ⟨Ha, %HI, Hvl, Hvr⟩ HΦ'
          simp only [kvsOrEmpty, Option.getD_some] at Hst ⊢
          have hk := (zipKeys_mem_law_holds (some l) (some r) k).1 (by simpa [mapIterStep] using Hst.1)
          simp only [kvsOrEmpty, Option.getD_some] at hk
          wp_auto
          cases hlk : lookupKV k l with
          | none =>
            cases hrk : lookupKV k r with
            | none => exfalso; simp [hlk, hrk] at hk
            | some y =>
              simp only [optValF]
              icases Hvl with %rfl
              wp_auto
              iapply HΦ'; simp only [Bool.false_eq_true, ↓reduceIte, optValF]; iframe
              ipureintro; try simp only [true_and]
              intro h; subst h; rw [hlk] at hrk; cases hrk
          | some x =>
            simp only [optValF]
            ihave %Hcl := isValF_concrete_law_holds vl _ x $$ Hvl
            obtain ⟨ql, rfl⟩ := Hcl
            cases hrk : lookupKV k r with
            | none =>
              simp only [optValF]
              icases Hvr with %rfl
              wp_auto
              iapply HΦ'; simp only [Bool.false_eq_true, ↓reduceIte, optValF]; iframe
              ipureintro; try simp only [true_and]
              intro h; subst h; rw [hlk] at hrk; cases hrk
            | some y =>
              simp only [optValF]
              ihave %Hcr := isValF_concrete_law_holds vr _ y $$ Hvr
              obtain ⟨qr, rfl⟩ := Hcr
              wp_auto
              wp_apply wp_EqualsUsing al _ _ (DFrac.own 1) (DFrac.own 1) x y $$ [Ha Hvl Hvr]
                as %e ⟨Ha, Hvl, Hvr, %He⟩
              · iframe
              try wp_auto
              cases e
              · iapply HΦ'; simp only [Bool.false_eq_true, ↓reduceIte]; iframe
                ipureintro; intro h; subst h; rw [hlk] at hrk; cases hrk
                exact absurd (He.2 rfl) (by simp)
              · iapply HΦ'; simp only [↓reduceIte]; iframe
                ipureintro
                intro k' hk'
                rcases List.mem_append.1 hk' with h | h
                · exact HI k' h
                · simp at h; subst h; rw [hlk, hrk, He.1 rfl]
        · ipureintro; simp
      iunfold mapIterPost at Hpost
      cases b
      · isimp at Hpost
        icases Hpost with %Hne
        try wp_auto
        iapply HΦ; iframe; ipureintro
        simp [Hne]
      · isimp at Hpost
        icases Hpost with ⟨%done, %Hperm, %Hd⟩
        try wp_auto
        iapply HΦ; iframe; ipureintro
        simp only [true_iff, Option.some.injEq]
        simp only [mapIterDone, Bool.false_eq_true, ↓reduceIte] at Hperm
        apply ValuePure.kvs_eq_of_lookups l r hsl hsr (by subst hn; omega)
        intro k hk
        apply Hd
        apply Hperm.mem_iff.2
        apply (zipKeys_mem_law_holds (some l) (some r) k).2
        right; simpa [kvsOrEmpty] using (ValuePure.lookupKV_isSome_iff k r).2 hk
    · rw [decide_eq_false hn]
      wp_auto
      iapply HΦ; iframe; ipureintro
      simp only [Bool.false_eq_true, false_iff, Option.some.injEq]
      intro h; subst h; exact hn (BitVec.eq_of_toInt_eq (by omega))

end proof

end smd
end EtcdGrove
end Perennial
