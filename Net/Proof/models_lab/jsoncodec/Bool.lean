/-
The proof of `jsoncodec.Bool` (`Net/Spec/models_lab/jsoncodec/Bool.lean`; #24 J2 batch 2b), in the
form of dsverify-lab's `String`/`Uint` proofs: `At`, then `ValueEnd` over the scanner's `true`/`false`
literal (`scanL_bool`).
-/
module

public import Net.Spec.models_lab.jsoncodec.Bool
public import Net.Spec.models_lab.jsoncodec.At
public import Net.Spec.models_lab.jsoncodec.ValueEnd
public import Net.Proof.models_lab.jsoncodec.DecBase

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace JsonScan

open Perennial

/-- A boolean's literal is one value to the scanner, whatever follows it. -/
theorem scanL_bool (x : Bool) (rest : List w8) :
    scanL (models_lab.jsoncodec.boolLit x ++ rest) true = (0, (models_lab.jsoncodec.boolLit x).length) := by
  cases x <;>
  · simp only [models_lab.jsoncodec.boolLit, scanL, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      List.nil_append]
    rw [goL_scalar (hs := by decide) (hc1 := by decide) (hc2 := by decide) (hc3 := by decide)]
    simp [scalarL, litL, show isDig 116#8 = false by decide, show isDig 102#8 = false by decide]

end JsonScan

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

theorem Bool.wp_proof (wp_At : At.spec (GF := GF) (hG := hG))
    (wp_ValueEnd : ValueEnd.spec (GF := GF) (hG := hG)) :
    Bool.spec (GF := GF) (hG := hG) := by
  intro b dq bs i x rest hb
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  have hlen : uint.nat i + (boolLit x).length ≤ bs.length := by
    have h1 : 1 ≤ (boolLit x).length := by cases x <;> decide
    have := congrArg List.length hb; rw [List.length_drop, List.length_append] at this; omega
  obtain ⟨d, ds, hdl⟩ : ∃ d ds, boolLit x = d :: ds := by
    cases x <;> exact ⟨_, _, rfl⟩
  have h0 : bs[uint.nat i]? = some d := by
    have := congrArg (fun l => l[0]?) hb; simp only [List.getElem?_drop] at this; simpa [hdl] using this
  have hd : (x = true ∧ d = W8 116) ∨ (x = false ∧ d = W8 102) := by
    cases x <;> simp [boolLit] at hdl <;> simp [hdl.1]
  have hsp : JsonScan.spB d = false := by
    rcases hd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hsk : JsonScan.skipEnd bs (uint.nat i) = uint.nat i := skipEnd_ns' bs _ d h0 hsp
  simp only [models_lab.jsoncodec.Set', models_lab.jsoncodec.Keep,
    models_lab.jsoncodec.TypeErr]
  wp_auto
  wp_apply (wp_At b dq bs i d (by omega) (by rw [hsk]; exact h0)) $$ Hs as Hs
  rw [hsk, show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hsc : JsonScan.scanL (bs.drop (uint.nat i)) true = (0, (boolLit x).length) := by
    rw [hb]; exact JsonScan.scanL_bool x rest
  wp_apply (wp_ValueEnd b dq bs i (by omega) (by rw [hsc])) $$ Hs as Hs
  rw [hsc]
  simp only
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [_root_.decide_true]
    wp_auto
    iapply HΦ; iexact Hs
  · simp only [show (W8 102 = W8 116) = False by decide, decide_false, _root_.decide_true]
    wp_auto
    iapply HΦ; iexact Hs

end proof

end models_lab.jsoncodec
end Perennial
