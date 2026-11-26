/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putgetk/decimal.lean`: every index is in
bounds (the loop's `s[j]` at `j < len(s)`, `s[0]` under `len(s) > 1`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.decimal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode Net

open Lean Elab Tactic Meta in
/-- Case on an innermost `decide p` of the goal (one whose `p` has no `decide`): `Hd : decide p = bd`,
`bd` split (`false`, `true`), and the conditions on `bd` simplified. -/
local elab "dcase" : tactic => do
  let isDec : Lean.Expr → Bool := fun e => e.isAppOfArity ``Decidable.decide 2
  let tgt ← instantiateMVars (← getMainTarget)
  let some d := tgt.find? (fun e => isDec e && !(e.appFn!.appArg!.find? isDec).isSome)
    | throwError "dcase: no decide in the goal"
  let dStx ← Term.exprToSyntax d
  let hd := mkIdent `Hd
  let bd := mkIdent `bd
  evalTactic (← `(tactic| (generalize $hd:ident : $dStx = $bd:ident; cases $bd:ident <;> cleanup_bool_decide <;>
    (try simp only [Bool.false_eq_true, Bool.true_eq_false, decide_true, decide_false, eq_self_iff_true,
      decide_eq_true_eq, ↓reduceIte]))))

set_option hygiene false in
/-- A loop condition's `Hif` as the proposition. -/
local macro "hif_prop" : tactic => `(tactic| (first
  | exact Hif
  | exact of_decide_eq_true Hif
  | exact of_decide_eq_true (go.intoVal_inj Hif)
  | (rw [intoVal_eq_iff] at Hif; exact of_decide_eq_true Hif)))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]

-- The digits' loop (hygiene off): every `s[j]` at `j < len(s)`.
set_option hygiene false in
local macro "dec_loop" : tactic => `(tactic| (
  ihave IH : iprop(∃ (j nv : w64), "j" ∷ j_ptr ↦ j ∗ "n" ∷ n_ptr ↦ nv ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j⌝) $$ [j n]
  · iexists _, _
    iframe
    ipureintro
    first | decide | rfl | word
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  dcase
  · (try wp_auto)
    iapply HΦ; itrivial
  have hlt : sint.Z j < sint.Z (W64 (s.length : Int)) := of_decide_eq_true Hd
  have hjl : sint.nat j < s.length := by word
  obtain ⟨c, hc⟩ : ∃ c, s[sint.nat j]? = some c := ⟨_, List.getElem?_eq_getElem hjl⟩
  (try wp_auto)
  simp only [Hj, ite_true, hc]
  (try wp_auto)
  dcase
  · (try wp_auto)
    dcase
    · (try wp_auto)
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      word
    · (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ; itrivial
  · (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ; itrivial))

theorem decimal.wp_proof : decimal.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  (try wp_auto)
  -- the length checks: `len(s) == 0 || len(s) > 5 || (len(s) > 1 && s[0] == '0')`
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
  dcase
  · (try wp_auto)
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    dcase
    · (try wp_auto)
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      dcase
      · (try wp_auto)
        dec_loop
      · -- `s[0]`, in bounds
        have h1 := of_decide_eq_true Hd
        have hl1 : 0 < s.length := by word
        obtain ⟨c0, hc0⟩ : ∃ c, s[0]? = some c := ⟨_, List.getElem?_eq_getElem hl1⟩
        (try wp_auto)
        simp only [show sint.nat (W64 0) = 0 from rfl, show (0 : Int) ≤ sint.Z (W64 0) from by decide,
          ite_true, hc0]
        (try wp_auto)
        dcase
        · (try wp_auto)
          dec_loop
        · (try wp_auto)
          iapply HΦ; itrivial
    · (try wp_auto)
      iapply HΦ; itrivial
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
