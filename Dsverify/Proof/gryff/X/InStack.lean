/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/InStack.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: `inStack` (generic `GF`; no caller: `strongconnect` tracks the stack by `Index`/`Lowlink`)
-/
module

public import Dsverify.Proof.gryff.X.Access

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.X

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [gryff_sem : src.gryff.Assumptions]

set_option goose.wp.extras true

/-- `inStack(w)`: whether `w` is on the stack (the global `stack`'s pointers). -/
theorem wp_inStack (ex w : Loc) (s : GoSlice) (ptrs : List Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ globalAddr src.gryff.stack ↦ s ∗
        s ↦* ptrs }}
      (App (Val (ex @!! go.GoType.PointerType src.gryff.Exec.ty @!! go!"inStack")) (Val #w))
    {{ RET #(decide (w ∈ ptrs)); globalAddr src.gryff.stack ↦ s ∗ s ↦* ptrs }} := by
  iintro %Φ ⟨#Hpkg, Hsg, Hs⟩ HΦ
  wp_method_call
  wp_call
  wp_auto
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave HI : (∃ (i : w64) (uv : Loc), "i" ∷ i_ptr ↦ i ∗ "u" ∷ u_ptr ↦ uv ∗
      "Hs" ∷ s ↦* ptrs ∗
      "%HI" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len ∧ w ∉ ptrs.take (sint.Z i).toNat⌝ : IProp GF)
    $$ [i u Hs]
  · iexists (W64 0), _
    iframe
    ipureintro; refine ⟨by decide, Hsl.2, by simp⟩
  wp_for HI
  wp_if_destruct
  · obtain ⟨hi0, hil, hnt⟩ := HI
    obtain ⟨pv, hpv⟩ : ∃ pv, ptrs[(sint.Z i).toNat]? = some pv :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hsl.1]; simp only [sint.nat, sint.Z] at *; omega)⟩
    rw [ite_eq_left (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len from ⟨hi0, Hif⟩)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) s (sint.Z i)
      ptrs _ pv hi0 $$ [$Hs] as Hs
    · ipureintro; exact hpv
    wp_if_destruct
    · -- found
      wp_for_post
      have hm : w ∈ ptrs := by rw [Hif]; exact List.mem_of_getElem? hpv
      rw [decide_eq_true hm]
      iapply HΦ
      iframe
    · wp_for_post
      iframe
      iexists (i + W64 1), pv
      iframe
      ipureintro
      have hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by have := Hsl.1; word
      refine ⟨by omega, by omega, ?_⟩
      rw [hi1, show (sint.Z i + 1).toNat = (sint.Z i).toNat + 1 by omega,
        List.take_succ, hpv]
      simp only [Option.toList, List.mem_append, List.mem_singleton, not_or]
      exact ⟨hnt, fun h => Hif h⟩
  · obtain ⟨hi0, hil, hnt⟩ := HI
    have hall : ptrs.length ≤ (sint.Z i).toNat := by
      rw [Hsl.1]; simp only [sint.nat, sint.Z] at *; omega
    rw [List.take_of_length_le hall] at hnt
    rw [decide_eq_false hnt]
    iapply HΦ
    iframe

end

end Perennial.gryff.X
