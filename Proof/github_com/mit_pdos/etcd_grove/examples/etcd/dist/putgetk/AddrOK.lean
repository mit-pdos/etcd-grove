/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putgetk/AddrOK.lean`: the split of `a` at its
separators (every `a[j]` at `j < len(a)`, every `a[start:j]` with `start ≤ j`), the five parts read with
`decimal` (`parts[j]` at `j < 5 = len(parts)`) into the array `n`, the bounds. `""` gives one part, so `false`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.AddrOK
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

/-- `dcase`, then `wp_auto` in both cases. -/
local macro "dcase'" : tactic => `(tactic| (dcase <;> (try wp_auto)))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]

/-- The array `n`'s `i`-th element, and the array back (`getElem!`: no proof inside the value, so that
`dcase` finds the comparisons on it). -/
theorem arr5_get (p : Loc) (na : List w64) (i : Int) (hl : na.length = 5) (h0 : 0 ≤ i) (h5 : i < 5) :
    (p ↦ (array.mk 5 na : GoArray w64 5) : IProp GF) ⊢
      arrayIndexRef w64 i p ↦ na[i.toNat]! ∗
        (arrayIndexRef w64 i p ↦ na[i.toNat]! -∗ p ↦ (array.mk 5 na : GoArray w64 5)) := by
  have hi : i.toNat < na.length := by omega
  rw [getElem!_pos na i.toNat hi]
  have h := array_acc (GF := GF) p i (DFrac.own 1) 5 (array.mk 5 na) (na[i.toNat]'hi) h0 (by simp)
  iintro H
  icases h $$ H with ⟨Hel, Hb⟩
  iframe Hel
  iintro Hel
  ihave Hb := Hb $$ Hel
  simp only [List.set_getElem_self]
  iexact Hb

set_option hygiene false in
/-- Load `n[i]` (hygiene off: `n_ptr`, `na`, `hna`, `Hn`). -/
local macro "nload_at" i:term : tactic => `(tactic| (
  icases arr5_get n_ptr na $i hna (by decide) (by decide) $$ Hn with ⟨Hel, Hb⟩
  (try wp_auto)
  ihave Hn := Hb $$ Hel
  (try wp_auto)))

open Lean Elab Tactic Meta in
/-- Load the element of `n` the goal's next load reads (the one `arrayIndexRef` of the goal). -/
local elab "nload" : tactic => do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun e => e.isAppOf ``arrayIndexRef)
    | throwError "nload: no array element in the goal"
  let args := e.getAppArgs
  let iStx ← Term.exprToSyntax args[args.size - 2]!
  evalTactic (← `(tactic| nload_at $iStx))

set_option hygiene false in
/-- A `return false` (inside a loop or not) (hygiene off). -/
local macro "ret_false" : tactic => `(tactic| (
  (try wp_for_post)
  (try wp_auto)
  iapply HΦ; ipureintro; intro _; rfl))

set_option hygiene false in
/-- The split loop, no separator at `j`: on. -/
local macro "cont_nosep" : tactic => `(tactic| (
  wp_for_post
  iframe
  iexists _, _, psl, ps
  iframe
  ipureintro
  refine ⟨by word, by word, by word, by word⟩))

set_option hygiene false in
/-- The split loop, a separator at `j`: `parts = append(parts, a[start:j])`, `start = j + 1`. -/
local macro "sep_append" : tactic => `(tactic| (
  rw [if_pos (show 0 ≤ sint.Z st ∧ sint.Z st ≤ sint.Z j ∧ sint.Z j ≤ (a.length : Int) by word)]
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %lp ⟨Hl, -⟩
  (try wp_auto)
  wp_apply wp_slice_append $$ [Hps Hcap Hl] as %psl' ⟨Hps, Hcap, -⟩
  · iframe
  (try wp_auto)
  wp_for_post
  iframe
  iexists _, _, psl', _
  iframe
  ipureintro
  refine ⟨by word, by word, by word, ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  word))

theorem AddrOK.wp_proof (wp_decimal : decimal.spec (GF := GF) (hG := hG)) :
    AddrOK.spec (GF := GF) (hG := hG) := by
  intro a
  wp_start
  (try wp_auto)
  -- the split at the separators
  ihave IH : iprop(∃ (j st : w64) (psl : GoSlice) (ps : List GoString),
      "j" ∷ j_ptr ↦ j ∗ "start" ∷ start_ptr ↦ st ∗ "parts" ∷ parts_ptr ↦ psl ∗
      "Hps" ∷ psl ↦* ps ∗ "Hcap" ∷ ownSliceCap GoString psl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z st ∧ sint.Z st ≤ sint.Z j ∧ sint.Z j ≤ (a.length : Int) ∧
        ps.length ≤ sint.nat j⌝) $$ [j start parts]
  · iexists _, _, _, []
    iframe
    rw [show (zero_val GoSlice : GoSlice) = slice.nil from rfl]
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    ipureintro; refine ⟨by decide, Int.le_refl _, by simp, by simp⟩
  wp_for IH
  obtain ⟨hst0, hstj, hjl, hpl⟩ := Hj
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hal
  dcase
  rotate_left
  · have hlt : sint.Z j < sint.Z (W64 (a.length : Int)) := of_decide_eq_true Hd
    (try wp_auto)
    have hj0 : 0 ≤ sint.Z j := by omega
    have hjn : sint.nat j < a.length := by word
    obtain ⟨c, hc⟩ : ∃ c, a[sint.nat j]? = some c := ⟨_, List.getElem?_eq_getElem hjn⟩
    iterate 12 (all_goals (try (first
      | (simp only [hj0, ite_true, hc]; (try wp_auto))
      | dcase')))
    all_goals (try ret_false)
    -- no separator: on
    all_goals (try cont_nosep)
    -- a separator: `parts = append(parts, a[start:j])`, `start = j + 1`
    all_goals sep_append
  -- the last part, `a[start:]`
  have hge : ¬ sint.Z j < sint.Z (W64 (a.length : Int)) := of_decide_eq_false Hd
  have hja : sint.nat j = a.length := by word
  (try wp_auto)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  rw [if_pos (show 0 ≤ sint.Z st ∧ sint.Z st ≤ sint.Z (W64 (a.length : Int)) ∧
    sint.Z (W64 (a.length : Int)) ≤ (a.length : Int) by word)]
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %lp ⟨Hl, -⟩
  (try wp_auto)
  wp_apply wp_slice_append $$ [Hps Hcap Hl] as %psl' ⟨Hps, Hcap, -⟩
  · iframe
  ihave %Hpsl := ownSlice_len $$ Hps
  (try wp_auto)
  -- `len(parts) != 5`
  generalize Hd5 : decide (psl'.len = W64 5) = b5
  cases b5
  · ret_false
  have h5 := of_decide_eq_true Hd5
  have ha : a ≠ [] := by
    intro h
    subst h
    rw [h5, show sint.nat (W64 5) = 5 from rfl, List.length_append] at Hpsl
    simp only [List.length_cons, List.length_nil] at Hpsl hja
    omega
  (try wp_auto)
  -- the parts read into `n`
  generalize hP : ps ++ _ = P at Hpsl ⊢
  have hP5 : P.length = 5 := by rw [Hpsl.1, h5]; rfl
  ihave IN : iprop(∃ (j : w64) (na : List w64), "j" ∷ j_ptr ↦ j ∗
      "Hn" ∷ n_ptr ↦ (array.mk 5 na : GoArray w64 5) ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ na.length = 5⌝) $$ [j n]
  · iexists _, List.replicate 5 (W64 0)
    iframe
    ipureintro
    exact ⟨by first | decide | rfl | word, rfl⟩
  wp_for IN
  obtain ⟨hj0, hna⟩ := Hj
  dcase
  rotate_left
  · have hlt : sint.Z j < sint.Z (W64 5) := of_decide_eq_true Hd
    have hj5 : sint.nat j < 5 := by word
    obtain ⟨x, hx⟩ : ∃ x, P[(sint.Z j).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (show (sint.Z j).toNat < P.length by rw [hP5]; omega)⟩
    (try wp_auto)
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z psl'.len from ⟨hj0, by rw [h5]; exact hlt⟩,
      _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index psl' (sint.Z j) P (DFrac.own 1) x hj0) $$ [Hps] as Hps
    · iframe; ipureintro; exact hx
    wp_apply (wp_decimal x) as %v %ok -
    (try wp_auto)
    cases ok
    · (try wp_auto)
      wp_for_post
      (try wp_auto)
      iapply HΦ; ipureintro; intro _; rfl
    (try wp_auto)
    have h5' : sint.Z (W64 5) = 5 := rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < 5 by omega))]
    icases array_acc (GF := GF) n_ptr (sint.Z j) (DFrac.own 1) 5 (array.mk 5 na)
      (na[(sint.Z j).toNat]'(by omega)) hj0 (by simp) $$ Hn with ⟨Hel, Hb⟩
    (try wp_auto)
    ihave Hn := Hb $$ Hel
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by simp [hna]⟩
  -- the bounds
  (try wp_auto)
  iterate 40 (all_goals (try (first
    | nload
    | dcase')))
  all_goals (iapply HΦ; ipureintro; intro h; exact absurd h ha)

end proof

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
