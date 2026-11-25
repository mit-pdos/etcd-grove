/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Done.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): witnessing a reply (`opDone`) from lower bounds of the linearization and
of the history.
-/
module

public import Dsverify.Proof.gryff.Proto2P.Ghost
public import Dsverify.Proof.gryff.Proto.ClientLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness
open model kahn pure p2

section
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

theorem opDone_of (γ : ProtoNames) (L : List (OpId × RegOutput w64)) (l : List Label) (id : OpId)
    (o : RegOutput w64) (hin : (id, o) ∈ L) (hnd : (L.map Prod.fst).Nodup)
    (hr : repliedIn l id) :
    monoListLbOwn (GF := GF) γ.lin L ∗ histLb γ l ⊢ opDone γ id o := by
  unfold opDone
  iintro ⟨HL, Hl⟩
  isplitl [HL]
  · iexists L
    iframe HL
    ipureintro; exact ⟨hin, hnd⟩
  · iexists l
    iframe Hl
    ipureintro; exact hr

/-- Every reply of a list, from the lower bounds. -/
theorem opDone_all (γ : ProtoNames) (L : List (OpId × RegOutput w64)) (l : List Label)
    (xs : List Ext) (hnd : (L.map Prod.fst).Nodup)
    (h : ∀ x ∈ xs, (x.keyZ, x.out) ∈ L ∧ repliedIn l x.keyZ) :
    monoListLbOwn (GF := GF) γ.lin L ∗ histLb γ l ⊢ [∗list] x ∈ xs, opDone γ x.keyZ x.out := by
  iintro ⟨#HL, #Hl⟩
  iapply (BigSepL.bigSepL_intro (P := iprop(□ (monoListLbOwn (GF := GF) γ.lin L ∗ histLb γ l)))
    (fun i x hx => by
      have hm := List.mem_of_getElem? hx
      exact intuitionistically_elim.trans
        (opDone_of γ L l x.keyZ x.out (h x hm).1 hnd (h x hm).2)))
  imodintro
  iframe HL Hl

end

end Perennial.gryff
