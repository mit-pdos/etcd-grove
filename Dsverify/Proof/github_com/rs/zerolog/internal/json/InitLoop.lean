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

/-- `init.«0»` (`string.go:9`): with `noEscapeTable` owned, it returns with the table owned. -/
theorem wp_init0 (a : GoArray Bool 256) :
    {{ globalAddr noEscapeTable ↦ a }}
      (App (Val (@! init.«0»)) (Val #()))
    {{ RET #(); ∃ b : GoArray Bool 256, globalAddr noEscapeTable ↦ b }} := by
  wp_start as Ht
  wp_auto
  ihave HI : (∃ (k : w64) (b : GoArray Bool 256), "i" ∷ i_ptr ↦ k ∗
      "Ht" ∷ globalAddr noEscapeTable ↦ b ∗ "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 127⌝ : IProp GF)
      $$ [i Ht]
  · iexists (W64 0), a; iframe; ipureintro; decide
  wp_for HI
  wp_if_destruct
  · have hb : b.arr.length = 256 := by sorry
    obtain ⟨v, hv⟩ : ∃ v, b.arr[(sint.Z k).toNat]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [hb]; word)⟩
    sorry
  · iapply HΦ
    iexists b
    iexact Ht

end proof

end github_com.rs.zerolog.internal.json
end Perennial
