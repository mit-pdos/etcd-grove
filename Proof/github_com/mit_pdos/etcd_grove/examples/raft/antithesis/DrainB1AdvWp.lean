/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E: toward `DrainB1Phases.lean`'s
`drainAdvanceB1.stmt` (`node.drain.tailE`: `reads`, `applyCommitted`, `Advance`, the `sent` loop).
This part: the reports' pieces. The `read` reports (`readsAfter_intro`: per read state, `report_upd`
at `readHstep`, the read's index past every committed length its context was asked at from
`readsOwn` and raft's `readStateRaw`, `reads_fl`), the `apply` report's event (`applyEv_eq`,
`evApply_numsOk_b1`), the cause cell peeked when nothing is reported (`causeOwn_peek`), `Advance`
without a snapshot in the Sim's vocabulary (`advanceNoSnap_of`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1SendWp
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1ReadStates
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__reads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__applyCommitted
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sent
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `reads`' report of a read state within `2 ^ 61` at node `id` is the Sim's `evRead`. -/
theorem readEv_eq (id : w64) (r : ReadStateM) (h : uint.Z r.Index' < 2 ^ 61) :
    atNode (AntSim.nameOf id) (readEvM r) = AntSim.evRead id r.RequestCtx' r.Index' := by
  have e : sint.Z r.Index' = uint.Z r.Index' := by word
  unfold atNode readEvM AntSim.evRead
  rw [e]

theorem evRead_numsOk (id : w64) (ctx : List w8) (i : w64) (h : uint.Z i < 2 ^ 61) :
    (AntSim.evRead id ctx i).NumsOk := by
  have h0 : 0 ≤ uint.Z i := by word
  simp only [AntSim.evRead, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntCheck.numOk,
    AntCheck.numBound]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  all_goals omega

theorem evRead_chgOk (id : w64) (ctx : List w8) (i : w64) : (AntSim.evRead id ctx i).ChgOk 0 := by
  simp [AntCheck.Event.ChgOk, AntCheck.Event.entryLists, AntSim.evRead]

theorem evRead_weight (id : w64) (ctx : List w8) (i : w64) : (AntSim.evRead id ctx i).weight = 2 := by
  simp [AntCheck.Event.weight, AntCheck.Event.size, AntSim.evRead]

/-- Entries with terms below `2 ^ 61` read by `entryOf` as the binding's (`sint` is `uint`). -/
theorem entOfE_logOf {es : List EntryM} (h : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61) :
    es.map entOfE = AntSim.logOf es := by
  unfold AntSim.logOf
  apply List.map_congr_left
  intro e he
  have := h e he
  have e6 : sint.Z e.Term' = uint.Z e.Term' := by word
  unfold entOfE AntSim.entOf
  rw [e6]

/-- `applyCommitted`'s report of entries within `2 ^ 61` at node `id` is the Sim's `evApply`. -/
theorem applyEv_eq (id : w64) (b : AntCheck.Str) {es : List EntryM}
    (h : ∀ e ∈ es, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61) :
    atNode (AntSim.nameOf id) (applyEvM b es) = AntSim.evApply id b es := by
  have hf : sint.Z (firstIdx es) = AntSim.firstOf es := by
    cases es with
    | nil => simp only [firstIdx, AntSim.firstOf, List.head?_nil, Option.map_none, Option.getD_none]; rfl
    | cons e _ =>
      have := (h e List.mem_cons_self).2
      simp only [firstIdx, AntSim.firstOf, List.head?_cons, Option.map_some, Option.getD_some]
      word
  unfold atNode applyEvM AntSim.evApply
  rw [hf, entOfE_logOf (fun e he => (h e he).1)]

theorem evApply_numsOk_b1 {id : w64} {b : AntCheck.Str} {ce : List EntryM}
    (h : ∀ e ∈ ce, uint.Z e.Term' < 2 ^ 61 ∧ uint.Z e.Index' < 2 ^ 61) :
    (AntSim.evApply id b ce).NumsOk := by
  simp only [AntSim.evApply, AntCheck.Event.NumsOk, AntCheck.optNumOk, AntCheck.numOk,
    AntCheck.numBound, AntCheck.entriesOk, AntSim.logOf]
  and_intros
  all_goals try exact True.intro
  all_goals try (intro _ h; cases h; done)
  · cases ce with
    | nil => simp only [AntSim.firstOf]; omega
    | cons e _ =>
      have := (h e List.mem_cons_self).2
      simp only [AntSim.firstOf]; word
  · cases ce with
    | nil => simp only [AntSim.firstOf]; omega
    | cons e _ =>
      have := (h e List.mem_cons_self).2
      simp only [AntSim.firstOf]; word
  · intro es hes
    simp only [Option.some.injEq] at hes
    subst hes
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    have := (h e he).1
    unfold AntSim.entOf
    split
    · exact ⟨by word, by word⟩
    · split <;> exact ⟨by word, by word⟩

theorem evApply_weight_b1 (id : w64) (b : AntCheck.Str) (ce : List EntryM) :
    (AntSim.evApply id b ce).weight = ce.length + 2 := by
  simp [AntSim.evApply, AntCheck.Event.weight, AntCheck.Event.size, AntSim.logOf]

theorem evApply_chgOk (id : w64) (b : AntCheck.Str) (ce : List EntryM) :
    (AntSim.evApply id b ce).ChgOk 0 := by
  intro l hl e he
  simp only [AntCheck.Event.entryLists, AntSim.evApply, Option.getD_some, Option.map_none,
    Option.getD_none, List.nil_append, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hl
  subst hl
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
  exact Nat.le_of_eq (entOf_chgSize x)

/-- (antithesis parity B1) `Advance` without a snapshot, from raft's vocabulary to the Sim's. -/
theorem advanceNoSnap_of {Adm : List EntryM → CCState → Prop} {dec : CCDec} {k : NodeK} {id : w64}
    {r r' : RState} {qs : List Msg} (h : AdvanceEndRNoSnap Adm dec k id r qs r') :
    AntSim.AdvanceNoSnap Adm dec k id r qs r' := by
  induction h with
  | nil r r' ha => exact .nil _ _ ha
  | cons r r1 r' q qs hr _ ih => exact .cons _ _ _ _ _ hr ih

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- **The cause cell, when nothing is reported**: its pending report, given back unchanged. -/
theorem causeOwn_peek (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (cl : Loc) :
    causeOwn (GF := GF) γ j v cl ⊢
      ∃ o, pendingCause cl o ∗ (pendingCause cl o -∗ causeOwn γ j v cl) := by
  unfold causeOwn
  split
  · iintro (⟨%m, %Hm, Hpc, #Hw, Hr⟩ | ⟨%x, %Hx, Hpc, #Hw, Hr⟩)
    · iexists _
      iframe Hpc
      iintro Hpc
      ileft
      iexists m
      iframe Hpc Hw Hr
      ipureintro; exact Hm
    · iexists _
      iframe Hpc
      iintro Hpc
      iright
      iexists x
      iframe Hpc Hw Hr
      ipureintro; exact Hx
  · iintro Hpc
    iexists none
    iframe Hpc
    iintro Hpc
    iexact Hpc

theorem bigSepL_filter_drop {A : Type} (Φ : A → IProp GF) (p : A → Bool) :
    ∀ l : List A, ([∗list] x ∈ l, Φ x) ⊢ [∗list] x ∈ l.filter p, Φ x
  | [] => by simp only [List.filter_nil]; exact .rfl
  | a :: l => by
    rw [List.filter_cons]
    split
    · iintro H
      icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, Hl⟩
      iapply (BigSepL.bigSepL_cons).2
      iframe Ha
      iapply bigSepL_filter_drop Φ p l
      iexact Hl
    · iintro H
      icases (BigSepL.bigSepL_cons).1 $$ H with ⟨-, Hl⟩
      iapply bigSepL_filter_drop Φ p l
      iexact Hl

/-- **A read state's index is past every committed length its context was asked at**: the view's
request (`readsOwn`) and raft's certificate (`readStateRaw`) name the same committed log
(`readReq_agree`). `readHstep`'s `hfl`. -/
theorem reads_fl (γ : AntNames) (v : AntSim.NodeView) (st : ReadStateM) :
    readsOwn (GF := GF) γ v ∗ readStateRaw γ.raft.raftNames st ⊢
      ⌜∀ f, (st.RequestCtx', f) ∈ v.reads → f ≤ uint.nat st.Index'⌝ := by
  refine (forall_intro fun f => ?_).trans pure_forall.2
  refine (forall_intro fun hf => ?_).trans pure_forall.2
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hf
  iintro ⟨#Hro, #Hst⟩
  iunfold readsOwn at Hro
  ihave ⟨%Lc, #Hq, %Hle⟩ := BigSepL.bigSepL_lookup (Φ := fun _ (p : AntCheck.Str × Nat) =>
    iprop(∃ Lc : List EntryM, readReq γ.raft.raftNames p.1 Lc ∗ ⌜p.2 ≤ Lc.length⌝)) hi $$ Hro
  iunfold readStateRaw at Hst
  icases Hst with ⟨%c, %hc, Hok⟩
  iunfold EtcdGrove.readOk at Hok
  icases Hok with ⟨%Lc', #Hq', %Hle'⟩
  subst hc
  ihave %Heq := readReq_agree γ.raft.raftNames _ _ _ $$ Hq Hq'
  ipureintro
  subst Heq
  simp only at Hle
  have : (uint.nat st.Index' : Int) = uint.Z st.Index' := by word
  omega

/-- **The `read` reports** (`reads`' `readsAfter`): from the view `v` whose read states to report
are `L` (`Told`: the cause reported), each reported in order through `report_upd` at `readHstep`;
then `Φ` at a view with none left, the rest of `v` kept but its read requests (`readView` drops
the answered ones; `readsOwn` kept for what is left). -/
theorem readsAfter_intro (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (c : Loc) (γ : AntNames) (j : Fin γ.R.N)
    (hinm : ∀ S V net xnet, AntSim.AntSim γ.R γ.dec S V net xnet →
      AntSim.InMask AntSim.mskB1 γ.R net xnet) (Φ : IProp GF) :
    ∀ (L : List ReadStateM) (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg),
    v.rpend = L → AntSim.Told v → (∀ st ∈ L, uint.Z st.Index' < 2 ^ 61) →
    antCluster c γ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ readsOwn γ v ∗
      ([∗list] st ∈ L, readStateRaw γ.raft.raftNames st) ∗ viewFrag γ j v ∗ nodeLive γ j ∗
      (∀ (v' : AntSim.NodeView) (net : List Msg) (xnet : List XMsg),
        ⌜v' = { v with rpend := [], reads := v'.reads } ∧ net₀ <+: net ∧ xnet₀ <+: xnet⌝ -∗
        readsOwn γ v' -∗ sentLb γ net -∗ xsentLb γ xnet -∗ viewFrag γ j v' -∗ nodeLive γ j -∗ Φ) ⊢
    readsAfter γ.strm (AntSim.nameOf (AntSim.nodeId j)) L Φ
  | [], v, net₀, xnet₀, hrp, _, _ => by
    iintro ⟨#Hc, #Hlb, #Hxlb, #Hro, -, Hv, Hl, HΦ⟩
    simp only [readsAfter]
    iapply HΦ $$ %v %net₀ %xnet₀ [] Hro Hlb Hxlb Hv Hl
    ipureintro
    exact ⟨by rw [← hrp], List.prefix_refl _, List.prefix_refl _⟩
  | st :: L, v, net₀, xnet₀, hrp, htold, hidx => by
    iintro ⟨#Hc, #Hlb, #Hxlb, #Hro, Hst, Hv, Hl, HΦ⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hst with ⟨#Hst1, Hst⟩
    ihave %hfl := reads_fl γ v st $$ [$Hro $Hst1]
    simp only [readsAfter]
    iintro Hr
    have hi := hidx st List.mem_cons_self
    rw [readEv_eq _ st hi]
    iapply report_upd h_vu h_lo c γ j v (readView v st L) (AntSim.evRead (AntSim.nodeId j)
      st.RequestCtx' st.Index') net₀ [] xnet₀ [] (fun G0 G => G = G0) _
      (evRead_numsOk _ _ _ hi) (evRead_chgOk _ _ _)
      (readHstep j v st L net₀ xnet₀ hinm hrp htold hfl)
    iframe Hc Hlb Hxlb Hv Hl
    isplitl []
    · iapply factsExt_none
    isplitl [Hr]
    · rw [evRead_weight]; iexact Hr
    iintro ⟨Hv, Hl, %net, %xnet, #Hlb2, #Hxlb2, %Hp2⟩
    ihave #Hro2 : readsOwn (GF := GF) γ (readView v st L) $$ [Hro]
    · iunfold readsOwn
      iunfold readsOwn at Hro
      iapply bigSepL_filter_drop
      iexact Hro
    iapply readsAfter_intro h_vu h_lo c γ j hinm Φ L (readView v st L) net xnet rfl htold
      (fun s hs => hidx s (List.mem_cons_of_mem _ hs))
    iframe Hc Hlb2 Hxlb2 Hro2 Hst Hv Hl
    iintro %v' %net' %xnet' %Hv' Hro' Hlb' Hxlb' Hv Hl
    iapply HΦ $$ %v' %net' %xnet' [] Hro' Hlb' Hxlb' Hv Hl
    ipureintro
    obtain ⟨h1, h2, h3⟩ := Hv'
    exact ⟨h1, Hp2.1.trans h2, Hp2.2.2.1.trans h3⟩

end proof

end AntHarness
end EtcdGrove
end Perennial
