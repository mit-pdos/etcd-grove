/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/Writer.lean`: the outer loop's
invariant, no principal visited is named; the inner loop's, no prefix of the current principal
visited is a proper prefix of the key. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Principals
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The loops' pure steps -/

theorem keyPfx_length_le (x w : GoString) (hx : x ∈ keyParts) (hw : w ∈ principals) :
    (keyPfx x w).length ≤ 7 := by
  simp only [keyParts, principals, List.mem_cons, List.not_mem_nil, or_false] at hx hw
  rcases hx with rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;> decide

theorem take_mem_succ {α : Type} (l : List α) (j : Nat) (a : α) (h : l[j]? = some a)
    (P : α → Prop) (hP : ∀ b ∈ l.take j, P b) (ha : P a) : ∀ b ∈ l.take (j + 1), P b := by
  rw [List.take_add_one, h]
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact hP b hb
  · simp only [Option.toList_some, List.mem_singleton] at hb; subst hb; exact ha

/-- The first principal named is the writer. -/
theorem writerK_of_first (k w : GoString) (j : Nat) (hw : principals[j]? = some w)
    (hno : ∀ w' ∈ principals.take j, namesWho k w' = false) (h : namesWho k w = true) :
    writerK k = w := by
  unfold writerK
  have hsplit : principals = principals.take j ++ w :: principals.drop (j + 1) := by
    have := List.take_append_drop j principals
    rw [List.drop_eq_getElem?_toList_append, hw] at this
    simpa using this.symm
  rw [hsplit, List.find?_append, List.find?_eq_none.mpr (by
    intro b hb; simp [hno b hb])]
  simp [h]

/-- No principal named: `""`. -/
theorem writerK_none (k : GoString) (h : ∀ w ∈ principals, namesWho k w = false) :
    writerK k = [] := by
  unfold writerK
  rw [List.find?_eq_none.mpr (by intro b hb; simp [h b hb])]
  rfl

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem Writer.wp_proof (wp_Principals : Principals.spec (GF := GF) (hG := hG)) :
    Writer.spec (GF := GF) (hG := hG) := by
  intro k
  wp_start
  wp_auto
  wp_apply wp_Principals as %psl Hpsl
  ihave %Hpl := ownSlice_len $$ Hpsl
  ihave HI : (∃ (j : w64) (w0 : GoString),
      "i" ∷ i_ptr ↦ j ∗ "who" ∷ who_ptr ↦ w0 ∗ "Hpsl" ∷ psl ↦* principals ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z psl.len⌝ ∗
      "%Hno" ∷ ⌜∀ w ∈ principals.take (sint.nat j), namesWho k w = false⌝ : IProp GF)
      $$ [i who Hpsl]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    rw [show sint.nat (W64 0) = 0 by word]
    simp
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z psl.len :=
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z psl.len := ⟨Hj.1, Hlt⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem principals (sint.nat j) as w
    have hwm : w ∈ principals := List.mem_of_getElem? Hw_lookup
    wp_apply wp_load_slice_index psl (sint.Z j) principals (DFrac.own 1) w Hj.1 $$ [Hpsl] as Hpsl
    · iframe; ipureintro; exact Hw_lookup
    (try wp_auto)
    wp_apply wp_slice_literal (V := GoString) keyParts
    isplitr
    · ipureintro; rfl
    iintro %xsl ⟨Hxsl, -⟩
    simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
      show max (max (2 : Int) 0) 0 = 2 from rfl]
    (try wp_auto)
    rename_i oi_ptr
    ihave HJ : (∃ (n : w64) (x0 : GoString),
        "i" ∷ i_ptr ↦ n ∗ "x" ∷ x_ptr ↦ x0 ∗ "Hxsl" ∷ _ ↦* keyParts ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 2⌝ ∗
        "%Hnx" ∷ ⌜∀ x ∈ keyParts.take (sint.nat n), properPfx k (keyPfx x w) = false⌝ : IProp GF)
        $$ [i x Hxsl]
    · iexists W64 0, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [show sint.nat (W64 0) = 0 by word]
      simp
    wp_for HJ
    wp_if_destruct
    · have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 2) := ⟨Hn.1, Hif⟩
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      have Hnk : sint.nat n < keyParts.length := by rw [show keyParts.length = 2 from rfl]; word
      list_elem keyParts (sint.nat n) as x
      have hxm : x ∈ keyParts := List.mem_of_getElem? Hx_lookup
      have hpl := keyPfx_length_le x w hxm hwm
      simp only [keyPfx] at hpl
      have Hns : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      wp_apply wp_load_slice_index _ (sint.Z n) keyParts (DFrac.own 1) x Hn.1 $$ [Hxsl] as Hxsl
      · iframe; ipureintro; exact Hx_lookup
      (try wp_auto)
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hkl
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_if_destruct
      · -- `len(k) > len(p)`: the prefix compared
        have hlt : (x ++ go!"/" ++ w ++ go!"/").length < k.length := by word
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
        rw [ite_eq_left (by word)]
        have hs : sint.nat (W64 ((x ++ go!"/" ++ w ++ go!"/").length : Int)) - 0 =
            (x ++ go!"/" ++ w ++ go!"/").length := by word
        rw [hs, List.drop_zero]
        (try wp_auto)
        wp_if_destruct
        · -- a proper prefix: `w` is the writer
          (try wp_auto)
          wp_for_post
          wp_for_post
          have hnm : namesWho k w = true := by
            unfold namesWho
            rw [List.any_eq_true]
            refine ⟨x, hxm, ?_⟩
            simp only [properPfx, keyPfx, Bool.and_eq_true]
            exact ⟨decide_eq_true hlt, decide_eq_true Hif⟩
          rw [writerK_of_first k w _ Hw_lookup Hno hnm]
          iapply HΦ; itrivial
        · (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, x
          iframe
          ipureintro
          refine ⟨⟨by word, by word⟩, ?_⟩
          rw [Hns]
          refine take_mem_succ keyParts _ x Hx_lookup _ Hnx ?_
          simp only [properPfx, keyPfx, Bool.and_eq_false_iff]
          exact Or.inr (decide_eq_false Hif)
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, x
        iframe
        ipureintro
        refine ⟨⟨by word, by word⟩, ?_⟩
        rw [Hns]
        refine take_mem_succ keyParts _ x Hx_lookup _ Hnx ?_
        have hnl : ¬ (x ++ go!"/" ++ w ++ go!"/").length < k.length := by word
        simp only [properPfx, keyPfx, Bool.and_eq_false_iff]
        exact Or.inl (decide_eq_false hnl)
    · -- no prefix of `w`: the next principal
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, w
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]
      refine take_mem_succ principals _ w Hw_lookup _ Hno ?_
      have hn2 : sint.nat n = keyParts.length := by
        rw [show keyParts.length = 2 from rfl]; word
      rw [hn2, List.take_length] at Hnx
      unfold namesWho
      rw [List.any_eq_false]
      intro x hx
      simp [Hnx x hx]
  · (try wp_auto)
    have hj : sint.nat j = principals.length := by word
    rw [hj, List.take_length] at Hno
    rw [writerK_none k Hno]
    iapply HΦ; itrivial

end proof

end authkv
end EtcdGrove
end Perennial
