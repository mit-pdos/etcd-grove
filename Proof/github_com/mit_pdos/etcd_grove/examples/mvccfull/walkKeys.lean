/- Lean-first (no Rocq counterpart). The proof of `walkKeys` (by induction on `depth - len(p)`, its own spec for the recursive calls): Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.walkKeys
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem walkKeys.wp_proof :
    walkKeys.spec (GF := GF) (hG := hG) := by
  suffices H : ∀ (n : Nat) (s : GoSlice) (ks0 : List GoString) (p : GoString) (depth : w64),
      (p.length : Int) ≤ sint.Z depth → sint.nat depth - p.length = n →
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
          s ↦* ks0 ∗ ownSliceCap GoString s (DFrac.own 1) }}
        (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.walkKeys)) (Val #s))
          (Val #p)) (Val #depth))
      {{ (s' : GoSlice), RET #s'; s' ↦* (ks0 ++ walkM p n) ∗ ownSliceCap GoString s' (DFrac.own 1) }} by
    intro s ks0 p depth hp
    exact H _ s ks0 p depth hp rfl
  intro n
  induction n with
  | zero =>
    intro s ks0 p depth hp hn
    wp_start as ⟨Hs, Hcap⟩
    wp_auto
    wp_apply _root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len p as %Hpl
    wp_join iprop(∃ s1 : GoSlice, ks_ptr ↦ s1 ∗ s1 ↦* (ks0 ++ (if p = [] then [] else [p])) ∗
        ownSliceCap GoString s1 (DFrac.own 1) ∗ p_ptr ↦ p) with [ks Hs Hcap p] as ⟨%s1, ks, Hs, Hcap, p⟩
    · have hpne : p ≠ [] := by intro h; subst h; simp at Hif
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hosl] as %s1 ⟨Hs, Hcap, -⟩
      (try wp_auto)
      wp_join_done
      iexists s1; simp only [hpne, ↓reduceIte]; iframe
    · have hpe : p = [] := by
        apply List.eq_nil_of_length_eq_zero; have := Hif; word
      iexists s; simp only [hpe, ↓reduceIte, List.append_nil]; iframe
    wp_apply _root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len p as -
    have heq : W64 (p.length : Int) = depth := by word
    rw [decide_eq_true heq]
    (try simp only [↓reduceIte])
    (try wp_auto)
    iapply HΦ
    simp only [walkM]
    iframe
  | succ n ih =>
    intro s ks0 p depth hp hn
    wp_start as ⟨Hs, Hcap⟩
    wp_auto
    wp_apply _root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len p as %Hpl
    wp_join iprop(∃ s1 : GoSlice, ks_ptr ↦ s1 ∗ s1 ↦* (ks0 ++ (if p = [] then [] else [p])) ∗
        ownSliceCap GoString s1 (DFrac.own 1) ∗ p_ptr ↦ p) with [ks Hs Hcap p] as ⟨%s1, ks, Hs, Hcap, p⟩
    · have hpne : p ≠ [] := by intro h; subst h; simp at Hif
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hosl] as %s1 ⟨Hs, Hcap, -⟩
      (try wp_auto)
      wp_join_done
      iexists s1; simp only [hpne, ↓reduceIte]; iframe
    · have hpe : p = [] := by
        apply List.eq_nil_of_length_eq_zero; have := Hif; word
      iexists s; simp only [hpe, ↓reduceIte, List.append_nil]; iframe
    wp_apply _root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len p as -
    have hne : ¬ W64 (p.length : Int) = depth := by intro h; word
    rw [decide_eq_false hne]
    (try simp only [Bool.false_eq_true, ↓reduceIte])
    (try wp_auto)
    rw [show ([97#8] : GoString) = [W8 97] from rfl]
    wp_apply (ih s1 _ (p ++ [W8 97]) depth (by simp; word) (by simp; word)) $$ [$Hs $Hcap]
      as %s2 ⟨Hs, Hcap⟩
    (try wp_auto)
    rw [show ([98#8] : GoString) = [W8 98] from rfl]
    wp_apply (ih s2 _ (p ++ [W8 98]) depth (by simp; word) (by simp; word)) $$ [$Hs $Hcap]
      as %s3 ⟨Hs, Hcap⟩
    (try wp_auto)
    rw [show ([99#8] : GoString) = [W8 99] from rfl]
    wp_apply (ih s3 _ (p ++ [W8 99]) depth (by simp; word) (by simp; word)) $$ [$Hs $Hcap]
      as %s4 ⟨Hs, Hcap⟩
    (try wp_auto)
    iapply HΦ
    simp only [walkM, List.append_assoc]
    iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
