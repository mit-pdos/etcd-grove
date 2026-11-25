/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Step.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B: the critical section's step (`critical_step`'s proof): `replica_step`, `pendingOuts_step`,
and the trace's run (the invariant's `Inv2Facts.run`/`proj`, `kahn.grun_state`).
-/
module

public import Dsverify.Proof.gryff.Replica2.State
public import Dsverify.Proof.gryff.B.Pure

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open model kahn pure replica2
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A pure consequence, keeping the premise. -/
theorem keep_pure {PROP : Type _} [BI PROP] {P : PROP} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (and_intro .rfl h).trans persistent_and_sep_mp

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

theorem trace_agree (γ : ProtoNames) (k : Fin 3) (T : Fin 3 → List Ev) (t : List Ev) :
    monoListAuthOwn (GF := GF) (γ.s2.trace 0) (1 : Qp).half (T 0) ∗
      monoListAuthOwn (γ.s2.trace 1) (1 : Qp).half (T 1) ∗
      monoListAuthOwn (γ.s2.trace 2) (1 : Qp).half (T 2) ∗
      monoListAuthOwn (γ.s2.trace k) (1 : Qp).half t ⊢ ⌜T k = t⌝ := by
  iintro ⟨H0, H1, H2, Ht⟩
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by
    rcases k with ⟨_ | _ | _ | n, hk⟩
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
    · omega
  rcases hk3 with rfl | rfl | rfl
  · icases monoListAuthOwn_agree _ _ _ _ _ $$ H0 Ht with %h; ipureintro; exact h.2
  · icases monoListAuthOwn_agree _ _ _ _ _ $$ H1 Ht with %h; ipureintro; exact h.2
  · icases monoListAuthOwn_agree _ _ _ _ _ $$ H2 Ht with %h; ipureintro; exact h.2


/-- The invariant's body: replica `k`'s trace runs (unfolds `gryffInv2Body`, unit I's). -/
theorem body_trace_runs (γ : ProtoNames) (k : Fin 3) (t : List Ev) :
    gryffInv2Body (GF := GF) γ ∗ traceHalf γ k t ⊢
      gryffInv2Body γ ∗ traceHalf γ k t ∗ ⌜∃ o, runP gNet k t = some (stOf k t, o)⌝ := by
  unfold gryffInv2Body traceHalf
  iintro ⟨⟨%S, Hreg, H0, H1, H2, Hh, Hp, Hnp, Hid, Hb, Hl, Ho, Htu, Hc, Hpl, Hcr, Hrc, Hrx, Hrq,
    %Hf, Hops⟩, Ht⟩
  have hT : ∀ t', S.T k = t' → ∃ o, runP gNet k t' = some (stOf k t', o) := by
    intro t' ht'
    obtain ⟨c, hc⟩ := Hf.run
    obtain ⟨o, ho⟩ := grun_state hc k
    have hp := Hf.proj k
    refine ⟨o, ?_⟩
    have e1 : proj (N := gNet) S.l1 k = t' := by rw [← ht']; exact hp
    rw [e1] at ho
    unfold stOf
    split
    · rename_i h; have h2 := h.symm.trans ho; cases h2; exact ho
    · rename_i h; have h2 := h.symm.trans ho; cases h2
  icases keep_pure (trace_agree γ k S.T t) $$ [H0 H1 H2 Ht] with ⟨⟨H0, H1, H2, Ht⟩, %Hk⟩
  · iframe
  iframe Ht
  isplitl
  · iexists S; iframe; ipureintro; exact Hf
  · ipureintro; exact hT t Hk

/-- Replica `k`'s trace runs (the invariant's history is a run whose projections are the traces). -/
theorem trace_runs (γ : ProtoNames) (k : Fin 3) (t : List Ev) (E : CoPset) (hE : ↑gryffN ⊆ E) :
    gryffInv2 (GF := GF) γ ∗ traceHalf γ k t ⊢
      |={E}=> traceHalf γ k t ∗ ⌜∃ o, runP gNet k t = some (stOf k t, o)⌝ := by
  unfold gryffInv2
  have hb := body_trace_runs (GF := GF) γ k t
  unfold traceHalf at hb ⊢
  iintro ⟨#Hinv, Ht⟩
  iinv Hinv with Hi Hclose
  ihave Hl : ▷ (gryffInv2Body γ ∗ monoListAuthOwn (γ.s2.trace k) (1 : Qp).half t ∗
      ⌜∃ o, runP gNet k t = some (stOf k t, o)⌝) $$ [Hi Ht]
  · inext
    iapply hb $$ [Hi Ht]
    iframe
  icases Hl with ⟨Hi, >Ht, >%Hr⟩
  imod Hclose $$ Hi with -
  imodintro
  iframe
  ipureintro; exact Hr

end

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics] [fa : src.fastrpc.Assumptions]

/-- `critical_step`'s proof. -/
theorem critical_step_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (p : ProphId) (t : List Ev) (e : Ev) (s' : RState) (outs : List Out) :
    ⌜model.stepR k (pure.stOf k t) e = .ok (s', outs)⌝ ∗
        gryffInv2 γ.proto ∗ predsSet γ.proto ∗ traceHalf γ.proto k t ∗
        replicaProph γ.proto k p t (model.evCodec.enc e) ∗ evTok γ.proto k e ∗ £ 2 ∗
        pendingOuts γ ρ k r t [] ⊢
      |={⊤}=> traceHalf γ.proto k (t ++ [e]) ∗ replicaProph γ.proto k p (t ++ [e]) [] ∗
        pendingOuts γ ρ k r (t ++ [e]) outs ∗ ⌜pure.stOf k (t ++ [e]) = s'⌝ := by
  iintro ⟨%Hs, #Hinv, #Hpreds, Ht, Hp, Hev, Hlc, Hpo⟩
  imod trace_runs γ.proto k t ⊤ (by simp) $$ [Ht] with ⟨Ht, %Hrun⟩
  · iframe; iframe #
  imod replica_step γ.proto k p t e s' outs ⊤ rfl $$ [Ht Hp Hev Hlc] with
    ⟨Ht, #Hlb, Hp, %Hstr, Hdone⟩
  · iframe; iframe #; ipureintro; exact Hs
  imodintro
  iframe Ht Hp
  isplitl
  · iapply pendingOuts_step γ ρ k r t e outs Hstr $$ [Hpo Hdone]
    iframe; iframe #
  · ipureintro; exact stOf_snoc k t e s' outs Hrun Hs

/-- The recovery trigger's lower bound against the heap's `crtInstance[q]`. -/
theorem replicaOwnX_crtLb_le (ρ : Repl2Names) (k : Fin 3) (r : Loc) (xs : replica.XS)
    (s : RState) (q : Fin 3) (n : Nat) :
    replicaOwnX ρ k r xs s ∗ monoNatLbOwn (ρ.crt q) n ⊢
      replicaOwnX ρ k r xs s ∗ ⌜n ≤ (sint.Z (s.crt (replica2.rid32 q))).toNat⌝ := by
  iintro ⟨Hown, Hlb⟩
  icases (replicaOwnX_split ρ k r xs s).1 $$ Hown with
    ⟨%gR0, %pa, %co, %h0, #H1, #H2, #H3, #H4, Hparti, Hval, Hcoord, Hep, Hxs, Hprop, Hscr, %Hid⟩
  icases epaxosOwn_crtLb_le ρ h0 r xs s q n $$ [Hep Hlb] with ⟨Hep, %Hle⟩
  · iframe
  isplitl
  · iapply (replicaOwnX_split ρ k r xs s).2
    iexists gR0, pa, co, h0; iframe; iframe #; ipureintro; exact Hid
  · ipureintro; exact Hle

/-- **A run-loop case's critical section** (after the lock, the resolution and the step's `.ok`):
the handler's precondition (the heap at `stOf k t`, the obligations of the step at `t ++ [e]`)
and, from the handler's postcondition, the lock's contents at `t ++ [e]`. -/
theorem loop_step_open (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (pr : ProphId) (t : List Ev) (xs : replica.XS) (e : Ev)
    (hok : ∃ s' o, model.stepR k (pure.stOf k t) e = .ok (s', o)) :
    gryffInv2 γ.proto ∗ predsSet γ.proto ∗ evTok γ.proto k e ∗ £ 1 ∗ £ 1 ∗
        traceHalf γ.proto k t ∗ replicaProph γ.proto k pr t ([] ++ model.evCodec.enc e) ∗
        replicaOwnX ρ k r xs (pure.stOf k t) ∗ pendingOuts γ ρ k r t [] ∗
        ghostVar ρ.boot (1 : Qp).half false ⊢
      |={⊤}=> ∃ (s' : RState) (outs : List Out),
        ⌜model.stepR k (pure.stOf k t) e = .ok (s', outs)⌝ ∗
        replicaOwn ρ k r (pure.stOf k t) ∗ pendingOuts γ ρ k r (t ++ [e]) outs ∗
        (replicaOwn ρ k r s' -∗ pendingOuts γ ρ k r (t ++ [e]) [] -∗
          ∃ (t' : List Ev) (xs' : replica.XS), lockedAt γ ρ k r pr t' xs') := by
  obtain ⟨s', outs, hs⟩ := hok
  iintro ⟨#Hinv, #Hpreds, Hev, Hlc1, Hlc2, Ht, Hp, Hown, Hpo, Hboot⟩
  simp only [List.nil_append]
  ihave Hlc : £ 2 $$ [Hlc1 Hlc2]
  · iapply (lc_split (n := 1) (m := 1)).2; iframe
  imod critical_step_proof γ ρ k r pr t e s' outs $$ [Ht Hp Hev Hlc Hpo] with
    ⟨Ht, Hp, Hpo, %Hst⟩
  · iframe; iframe #; ipureintro; exact hs
  imodintro
  iexists s', outs
  isplitr
  · ipureintro; exact hs
  isplitl [Hown]
  · unfold replicaOwn; iexists xs; iexact Hown
  iframe Hpo
  iintro Hown Hpo
  unfold replicaOwn
  icases Hown with ⟨%xs', Hown⟩
  iexists t ++ [e], xs'
  unfold lockedAt
  rw [Hst]
  iframe

end

end Perennial.gryff.unitB
