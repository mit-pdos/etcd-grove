/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/ViewHelpers.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
Helpers of the view-change handlers (agent RB): dropping a key of a map's big separating
conjunction, and the pending PrepareOK entries of a replica that is not the normal primary.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.DoViewChange

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


set_option linter.unusedSectionVars false

section helpers
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-- Dropping a key of a map's big separating conjunction. -/
theorem replica.bigSepM_drop {V : Type} (Φ : w64 → V → IProp GF) (m : GMap w64 V)
    (k : w64) : ([∗map] k' ↦ x ∈ m, Φ k' x) ⊢ [∗map] k' ↦ x ∈ GMap.delete k m, Φ k' x := by
  cases h : m !! k with
  | none => rw [GMap.delete_notin m k h]
  | some x =>
    iintro H
    icases (BI.BigSepM.bigSepM_delete (M := GMap w64) (Φ := Φ) h).1 $$ H with ⟨-, H⟩
    iexact H

/-- A pending PrepareOK entry stays valid for a replica that is not the normal primary. -/
theorem replica.pokOk_notPrimary (γ : VsrGhost.Names) (n : Nat) (tcp : Loc)
    (v v' : replica.Replica)
    (r : Nat) (k : w64) (e : replica.PendingPrepareOK) (hn : ¬ replica.IsNormalPrimary n v' r) :
    replica.pokOk (GF := GF) γ n tcp v r k e ⊢ replica.pokOk γ n tcp v' r k e := by
  unfold replica.pokOk
  iintro ⟨%rs, Hm, Ha, -⟩
  iexists rs
  iframe Hm Ha
  simp only [hn, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
  itrivial

end helpers

end Perennial.github_com.tangledbytes.go_vsr.pkg
