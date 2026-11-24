/-
`netN.StringsIndexHyp` (`Dsverify/Proof/gryff/N/StrIndex.lean`) holds, without a new axiom:
Perennial's `strings.Index` (translated with its body since Perennial `fce59af75`) on the one-byte
path of `stringslite.Index`, over Perennial's proof of `stringslite.IndexByte` (pin-bump-fce59af75).
`stringsIndexHyp_holds` discharges the class in `gryff_remote_robust`'s proof (the statement had it
as a premise until 2026-11-24); a defs module, moved out of `NonVacuityLinked.lean` (name unchanged)
so that the proof needs no test-only module (CLAUDE.md, "Import tiers").
-/
module

public import Dsverify.Proof.gryff.N.StrIndex
public import Perennial.Proof.internal.stringslite.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace gryff.examples.gryffnet.instances

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Perennial.gryff

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ### `netN.StringsIndexHyp`: Perennial's `strings.Index` (translated with its body since
Perennial `fce59af75`), on the one-byte path of `stringslite.Index`, which reads no package
variable (so it holds with the class's `True` precondition, without `isPkgInit`) -/

section strindex
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [_root_.Perennial.strings.Assumptions]

theorem getElem?_ne_of_lt_idxOf {c : w8} :
    ∀ (s : List w8) (j : Nat), j < s.idxOf c → s[j]? ≠ some c
  | [], j, h => by simp at h
  | a :: t, j, h => by
    rw [List.idxOf_cons] at h
    cases j with
    | zero =>
      intro he
      simp only [List.getElem?_cons_zero, Option.some_inj] at he
      subst he
      simp at h
    | succ j =>
      simp only [List.getElem?_cons_succ]
      have h' : j < t.idxOf c := by
        cases hb : (a == c) <;> simp [hb] at h
        omega
      exact getElem?_ne_of_lt_idxOf t j h'

theorem indexByte_eq_indexOfByte (s : GoString) (c : w8) :
    internal.bytealg.indexByte s c = netN.indexOfByte s c := by
  unfold netN.indexOfByte
  split
  · rename_i hm
    have hlt : s.idxOf c < s.length := List.idxOf_lt_length_iff.2 hm
    refine internal.bytealg.indexByte_eq_of s c _ ?_ ?_
    · rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
    · exact fun j hj => getElem?_ne_of_lt_idxOf s j hj
  · rename_i hm
    exact internal.bytealg.indexByte_eq_neg s c (fun j hj => hm (List.mem_of_getElem? hj))

/-- `stringslite.Index(s, string(c))`: its `n == 1` case, `IndexByte(s, c)`; no package variable is
read before it. -/
theorem wp_stringslite_Index_byte (s : GoString) (c : w8) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.internal.stringslite.Index')) (Val #s))
        (Val #([c] : GoString)))
    {{ RET #(W64 (internal.bytealg.indexByte s c)); True }} := by
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hn
  wp_if_destruct
  · exfalso; simp only [eq_comm (a := true), decide_eq_true_eq] at Hif; revert Hif; simp
  wp_if_destruct
  · try wp_auto
    wp_apply internal.stringslite.wp_IndexByte as %Hsl
    iapply HΦ
    itrivial
  · exfalso; simp only [eq_comm (a := true), decide_eq_true_eq] at Hif; revert Hif; simp

theorem stringsIndexHyp_holds : netN.StringsIndexHyp GF := by
  constructor
  intro s c
  wp_start
  wp_auto
  wp_apply wp_stringslite_Index_byte
  rw [indexByte_eq_indexOfByte]
  iapply HΦ
  itrivial

end strindex

end gryff.examples.gryffnet.instances
end Perennial
