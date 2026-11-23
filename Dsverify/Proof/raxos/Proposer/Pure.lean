/-
Package `proposer`: the consensus steps of `handleProposeRequest` (`Pure/Consensus.lean`'s `Step`)
from the facts the code has, and their ghost counterparts (`cons_step`).
-/
module

public import Dsverify.Proof.raxos.Cons.Laws

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure

namespace prop

/-- A reply collected by an iteration: from peer `g.1` (recorder `g.1 + 1`), for the value
`g.2.1`, with the recorder's state `g.2.2`. -/
abbrev Got := Nat × pure.Val × RecSt

/-- The `record` event of a collected reply. -/
def gotEv (i s : Int) (g : Got) : Ev := .record ((g.1 + 1 : Nat) : Int) i s g.2.1 g.2.2

/-- A majority (`n / 2 + 1`) of replies from distinct peers of `0..n-1` (recorders `1..n`), each
with a positive step and for a variant of `P`, whose `record` events are in `W`. -/
theorem replies_got (n : Nat) (W : World) (i : Int) (lead : Bool) (s : Int) (P : pure.Val)
    (got : List Got) (hlen : got.length = n / 2 + 1) (hnd : (got.map Prod.fst).Nodup)
    (hall : ∀ g ∈ got, g.1 < n ∧ 0 < g.2.2.S ∧ variants lead s P g.2.1)
    (hW : ∀ g ∈ got, gotEv i s g ∈ W) :
    Replies (n : Int) W i lead s P (got.map (fun g => g.2.2)) := by
  refine ⟨got.map (fun g => ((g.1 + 1 : Nat) : Int)), got.map (fun g => g.2.1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, hlen]; omega
  · simp
  · simp
  · have : got.map (fun g => ((g.1 + 1 : Nat) : Int)) =
        (got.map Prod.fst).map (fun j => ((j + 1 : Nat) : Int)) := by simp [List.map_map]
    rw [this]
    exact List.Pairwise.map _ (fun a b h => by omega) hnd
  · intro r hr
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
    have := (hall g hg).1
    omega
  · intro k r v st hr hv hst
    simp only [List.getElem?_map] at hr hv hst
    cases hk : got[k]? with
    | none => rw [hk] at hr; cases hr
    | some g =>
      rw [hk] at hr hv hst
      simp only [Option.map_some, Option.some.injEq] at hr hv hst
      subst hr hv hst
      have hg := List.mem_of_getElem? hk
      exact ⟨(hall g hg).2.1, hW g hg, (hall g hg).2.2⟩

/-- Go's `S % 4 == c` on an `int`. -/
theorem srem4_eq (S : w64) (c : Int) (hc : 0 ≤ c ∧ c < 4) :
    (BitVec.srem S (W64 4) = W64 c) ↔ (sint.Z S).tmod 4 = c := by
  have h4 : sint.Z (W64 4) = 4 := by decide
  have hcc : sint.Z (W64 c) = c := by word
  constructor
  · intro h; have := congrArg BitVec.toInt h
    simp only [sint.Z] at h4 hcc ⊢; rw [BitVec.toInt_srem, h4, hcc] at this; exact this
  · intro h; apply BitVec.eq_of_toInt_eq
    simp only [sint.Z] at h4 hcc ⊢; rw [BitVec.toInt_srem, h4, hcc]; exact h

/-- Go's `S + 1` on an `int`. -/
theorem sint_add_one (S : w64) : sint.Z (S + W64 1) = wrapInc (sint.Z S) := by
  unfold wrapInc
  split
  · word
  · word

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A step justified by a known `pstate` and the collected replies' `record` events. -/
theorem ghost_stepR (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (c : QConf) (e0 : Ev)
    (i s : Int) (got : List Got) (e : Ev)
    (hstep : ∀ W : World, e0 ∈ W → (∀ g ∈ got, gotEv i s g ∈ W) → Step c.n c.ep W e)
    (hkind : ∀ i me ids lead, e ≠ .init i me ids lead)
    (hkind' : ∀ r i s v st, e ≠ .record r i s v st) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ confIs γ c -∗ evIn γ e0 -∗
      ([∗list] g ∈ got, evIn γ (gotEv i s g)) ={E}=∗ evIn γ e := by
  have hst : ∀ W : World, (∀ e' ∈ e0 :: got.map (gotEv i s), e' ∈ W) → Step c.n c.ep W e :=
    fun W hW => hstep W (hW _ (by simp)) (fun g hg => hW _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hg)))
  iintro #Hinv #Hc #H0 #Hg
  iapply cons_step γ E hE c (e0 :: got.map (gotEv i s)) e hst hkind hkind' $$ Hinv Hc
  iapply BigSepL.bigSepL_cons.2; isplitl; · iexact H0
  rw [BigSepL.bigSepL_map (gotEv i s)]
  iexact Hg

/-- A step justified by one known event. -/
theorem ghost_step1 (γ : QNames) (E : CoPset) (hE : ↑consN ⊆ E) (c : QConf) (e1 e : Ev)
    (hstep : ∀ W : World, e1 ∈ W → Step c.n c.ep W e)
    (hkind : ∀ i me ids lead, e ≠ .init i me ids lead)
    (hkind' : ∀ r i s v st, e ≠ .record r i s v st) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ confIs γ c -∗ evIn γ e1 ={E}=∗ evIn γ e := by
  have hst : ∀ W : World, (∀ e' ∈ [e1], e' ∈ W) → Step c.n c.ep W e := fun W hW =>
    hstep W (hW _ (by simp))
  iintro #Hinv #Hc #H1
  iapply cons_step γ E hE c [e1] e hst hkind hkind' $$ Hinv Hc
  iapply BigSepL.bigSepL_cons.2; isplitl; · iexact H1
  iapply BigSepL.bigSepL_nil.2; iempintro

end ghost

end prop

end Perennial.raxos
