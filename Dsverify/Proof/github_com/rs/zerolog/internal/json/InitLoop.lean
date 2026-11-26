/-
`internal/json`'s `init` (`string.go:9`, dsv-retire-3, 2026-11-26): the loop over `0..0x7e` that sets
`noEscapeTable[i]` for the printable characters but `\` and `"`. Its spec keeps only that the table
is still owned (its contents are not described: `internal/json`'s fact, `Base.lean`). Used by the
package's generated `Init.lean` (etc/dsv/rabia.py's `initfn_apply`).
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.internal.json.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.rs.zerolog.internal.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.internal.json.Assumptions]

/-- A store of the `i`-th entry of a `bool` array (`hash.crc32.wp_store_arr32`'s, at `bool`). -/
theorem wp_store_arrBool (l : Loc) (n : Int) (a : GoArray Bool n) (i : Int) (v : Bool)
    (hi : 0 ≤ i ∧ i < n) :
    {{ (l ↦ a : IProp GF) }}
      (App (Val (GoInstruction (GoStore go.bool))) (Val (PairV #(arrayIndexRef Bool i l) #v)))
    {{ RET #(); l ↦ (array.mk n (a.arr.set i.toNat v) : GoArray Bool n) }} := by
  iintro %Φ Ha HΦ
  obtain ⟨arr⟩ := a
  icases array_len _ _ _ _ $$ Ha with %Hlen
  have hlk : arr[i.toNat]? = some (arr.getD i.toNat false) := by
    rw [List.getElem?_eq_getElem (by omega)]
    simp [List.getD, List.getElem?_eq_getElem (show i.toNat < arr.length by omega)]
  icases array_acc _ i (DFrac.own 1) n ⟨arr⟩ (arr.getD i.toNat false) hi.1 hlk $$ Ha with ⟨Hv, Ha⟩
  wp_apply IntoValTyped.wp_store (t := go.bool) _ _ _ $$ Hv as Hv
  iapply HΦ
  iapply Ha $$ Hv

/-- `init.«0»` (`string.go:9`): with `noEscapeTable` owned, it returns with the table owned. -/
theorem wp_init0 (a : GoArray Bool 256) :
    {{ (globalAddr noEscapeTable ↦ a : IProp GF) }}
      (App (Val (@! init.«0»)) (Val #()))
    {{ RET #(); (∃ b : GoArray Bool 256, globalAddr noEscapeTable ↦ b : IProp GF) }} := by
  wp_start as Ht
  wp_auto
  ihave HI : (∃ (k : Nat) (b : GoArray Bool 256), "i" ∷ i_ptr ↦ W64 (k : Int) ∗
      "Ht" ∷ globalAddr noEscapeTable ↦ b ∗ "%Hk" ∷ ⌜k ≤ 127⌝ : IProp GF)
      $$ [i Ht]
  · iexists 0, a; iframe; ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hk : k ≤ 126 := by revert Hif; word
    have hb : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < 256 := by word
    all_goals try wp_auto
    all_goals try (wp_if_destruct)
    all_goals try wp_auto
    all_goals try (wp_if_destruct)
    all_goals try wp_auto
    all_goals try (wp_if_destruct)
    all_goals try wp_auto
    all_goals try rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    all_goals try wp_apply (wp_store_arrBool _ 256 _ _ _ hb) $$ Ht as Ht
    all_goals try wp_auto
    all_goals
      wp_for_post
      iframe
      iexists (k + 1), _
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe
      ipureintro; omega
  · iapply HΦ
    iexists b
    iexact Ht

end proof

end github_com.rs.zerolog.internal.json
end Perennial
