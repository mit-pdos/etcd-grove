/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on `MsgProp` at a leader: the lines'
pieces** (2026-11-11, trace-check Q8 stage 1 slice 22a, `notes/decisions.md`, "Q8 stage 1 (slice 22a)").

A leader's proposal logs one `Replicate` line per entry (`traceReplicate`, `"Hgprep"`), then the
self-acknowledgement's `SendAppendEntriesResponse` (`"Hgpack"`, at the state with the batch appended),
then one `SendAppendEntriesRequest` per peer (`"#Hgpapp"`). This file has the lines' phase steps:

- **the self-acknowledgement's** (`phaseStepB_selfAck`: `phaseStepB_send_pin` with
  `lineEffect_selfAck`, at a leader's state, `selfAck` being the protocol's `pselfAck`).

(2026-11-11, slice 24a, `notes/decisions.md`, "Q8 stage 1 (slice 24a)") And **the family's propose
update** (`ghost_stepProp`). The `Replicate` lines' phase steps and facts are in
`TracedRaftStepPropRep.lean`, the gates and the bundle in `TracedRaftStepPropBundle.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepHup

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- `appendEntry`'s self-acknowledgement is the protocol's (`pselfAck`): the new last index is the
log's last index. -/
theorem selfAck_eq_pselfAck (id : w64) (s : NState) : selfAck id s = pselfAck id (toPState s) := by
  have h : logLast s.logst = plastIndex (toPState s) := by
    simp only [logLast, plastIndex, plogLastIndexZ, toPState, List.length_append]
    push_cast; rw [Int.add_assoc]
  simp only [selfAck, pselfAck, h]
  rfl

end pure

section phases
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The self-acknowledgement's phase step, pinned** (`phaseStepB_send_pin` with `lineEffect_selfAck`),
at a leader's state `s1` (the proposal's appended state, on `MsgProp`'s path). -/
theorem phaseStepB_selfAck (id : w64) (c : CfgM) (s1 : NState) (o : List Msg)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length (selfAck id s1) = some ma0) (hrole : s1.role = .leader) :
    PhaseStepB id c (SendEvOf (W64 11) id s1 c (selfAck id s1)) (PinAt s1 C0 cs0 P0 o)
      (PinAt s1 C0 cs0 (P0 ++ [ma0]) (o ++ [selfAck id s1])) := by
  rw [selfAck_eq_pselfAck] at hma ⊢
  apply phaseStepB_send_pin id c s1 _ o _ C0 cs0 P0 ma0 hma rfl
    (fun e he => ⟨he.2.1, sendEvOf_notBoot he (by decide) (by decide) (by decide)⟩)
  intro C e a he hin hout hC hR hs bt bc bl
  exact ⟨_, rfl, lineEffect_selfAck C e id s1 c a _ he hin hout hC hR hs hrole bt bc bl⟩

end phases

section ghostProp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- `proposed` is `StepC.propose`'s state (`raft__Step/MsgProp.lean`'s `toPState_proposed`, which a
module outside `raft__Step/` may not import). -/
theorem toPState_proposed' (id : w64) (s : NState) (ents : List EntryM) :
    toPState (proposed id s ents) =
    psendMsgs
      (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))
      [pselfAck id
         (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))] := by
  have Hli : ∀ s : NState, plastIndex (toPState s) = logLast s.logst := by
    intro s
    simp only [plastIndex, plogLastIndexZ, logLast, toPState, List.length_append]
    congr 1; push_cast; omega
  simp only [proposed, sendMsgs, toPState, psendMsgs, pappend, pselfAck, selfAck, logAppend,
    List.append_assoc]
  rw [← Hli s]
  simp only [toPState]
  congr 3
  simp only [plastIndex, plogLastIndexZ, logLast, List.length_append]
  congr 2; push_cast; simp only [List.length_mapIdx]; omega

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- The conf-change loop keeps a batch of no conf-change entry whole (`raft__Step/MsgProp.lean`'s
`propConf_noConf_fold`). -/
theorem propConf_noConf_fold' (joint : Bool) (applied li : w64) (ents : List EntryM)
    (cs : List (Option ConfChangeIM)) (hct : CCTypesOk ents cs) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e) :
    ∀ acc : List EntryM × w64,
      (ents.zip cs).foldl (propConfStep joint applied li) acc = (acc.1 ++ ents, acc.2) := by
  revert hnc
  induction hct with
  | nil => intro _ acc; simp
  | @cons e o es os ho _ ih =>
    intro hnc acc
    have hn : o = none := by
      have h1 : o.isSome = false := by
        rw [ho]; simp only [decide_eq_false_iff_not]; exact hnc e (List.mem_cons_self ..)
      cases o with
      | none => rfl
      | some _ => simp at h1
    subst hn
    simp only [List.zip_cons_cons, List.foldl_cons, propConfStep]
    rw [ih (fun e' he' => hnc e' (List.mem_cons_of_mem _ he'))]
    simp

omit [GooseInterp] [GooseSemantics] go_gctx in
theorem propConf_noConf' (joint : Bool) (applied li pci : w64) (ents : List EntryM)
    (cs : List (Option ConfChangeIM)) (hct : CCTypesOk ents cs) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e) :
    propConf applied li pci ents cs joint = (ents, pci) := by
  unfold propConf
  rw [propConf_noConf_fold' joint _ _ ents cs hct hnc]
  simp

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- The proposed state's self-acknowledgement carries its numbers, below the bound. -/
theorem selfAck_trOk (id : w64) (s : NState) (hT : uint.Z s.term < traceNumBound)
    (hL : uint.Z (logLast s.logst) < traceNumBound) : (selfAck id s).TrOk := by
  apply Msg.trOk_of_nums (by simp [selfAck]) (by simp [selfAck])
  intro _
  have h0 : uint.nat (W64 0) = 0 := rfl
  have hb : (0 : Nat) < traceNumBound := by unfold traceNumBound; omega
  refine ⟨by simp only [selfAck]; word, by simp only [selfAck, List.length_nil]; exact hb,
    by simp only [selfAck, h0]; exact hb, by simp only [selfAck]; word,
    by simp only [selfAck, h0]; exact hb, by simp only [selfAck, h0]; exact hb⟩

/-- (2026-11-11, slice 24a) **The family's propose update** (`ownRaftGhost_step_propose`, a basic
update, and in the dynamic mode `RInv_propose`, pure): with what `Step` lends the `Replicate` gate
(`propLend`: the batch's entries' data, its tickets and the receipt covering its indices), raft's ghost
state moves from a leader's `s` to the proposed state (the batch appended, the self-acknowledgement
queued), at the same mode; no later credit (`£`) in either mode. For a batch of no conf-change entry
(a traced node's), at the terms' and the receipts' bounds (the self-acknowledgement's numbers, for
`NsLink`'s `OutTr`). Also gives the new last index's bound. -/
theorem ghost_stepProp (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (ents : List EntryM) (cs : List (Option ConfChangeIM))
    (hrole : s.role = .leader) (hct : CCTypesOk ents cs) (hnc : ∀ e ∈ ents, ¬ IsConfEnt e)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    (([∗list] e ∈ ents, propData γ e) ∗ ([∗list] e ∈ ents, entTk γ e) ∗
        ⧖ ((plogLastIndexZ (toPState s).base (toPState s).log).toNat - γ.reBoot.length + ents.length) ∗
        ownStepGhost γ md c id s : IProp GF) ⊢
      |={⊤}=> ⌜plogLastIndexZ (toPState s).base (toPState s).log + ents.length < traceNumBound⌝ ∗
        ownStepGhost γ md c id (proposed id s ents) := by
  iintro ⟨Hd, Htk, #Hrc, Hgh⟩
  icases ownStepGhost_bootCommit γ md c id s $$ Hgh with ⟨%Hbc, Hgh⟩
  iunfold ownStepGhost at Hgh
  icases Hgh with ⟨Hg, Hr⟩
  ihave %Hok := ownRaftGhost_logOk γ id (toPState s) $$ Hg
  ihave %Hlt := preceipt_lt _ $$ Hrc
  have hL0 := plogLastIndexZ_nonneg (toPState s).base (toPState s).log
  have hcm : (uint.Z s.logst.committed) ≤ plogLastIndexZ (toPState s).base (toPState s).log := Hok.2.2
  have hb : traceNumBound = 2 ^ 61 := rfl
  have hB : plogLastIndexZ (toPState s).base (toPState s).log + ents.length < traceNumBound := by
    omega
  have hrole' : (toPState s).role = .leader := by rw [toPState_role, hrole]; rfl
  ihave Hg := ownRaftGhost_step_propose γ id (toPState s) ents
    ((plogLastIndexZ (toPState s).base (toPState s).log).toNat - γ.reBoot.length + ents.length)
    hrole' (by omega) (by omega) $$ Hrc Hd Htk [] Hg
  · iintro !> %fp' %k %x %Hx
    exfalso
    obtain ⟨-, hk, -, hv2⟩ := Hx
    rw [List.getElem?_mapIdx] at hk
    cases he : ents[k]? with
    | none => rw [he] at hk; cases hk
    | some e =>
      rw [he] at hk; cases hk
      exact hnc e (List.mem_of_getElem? he) (.inr hv2.2)
  imod Hg with Hg
  rw [show (toPState s).term = s.term from rfl, ← toPState_proposed']
  imodintro
  isplitr
  · ipureintro; exact hB
  iunfold ownStepGhost
  iframe Hg
  iunfold ghostRest at Hr
  icases Hr with ⟨%Hn, Hm, #Hcl, #Hw, #Hx⟩
  have hlw : leadW (GF := GF) γ id (toPState (proposed id s ents)) = leadW γ id (toPState s) := by
    unfold leadW; rfl
  have hxw : xfW (GF := GF) γ (proposed id s ents) = xfW γ s := rfl
  have hgh : (proposed id s ents).gh = s.gh := rfl
  iunfold ghostRest
  rw [hlw, hxw, hgh]
  iframe Hcl Hw Hx
  isplitr
  · ipureintro
    refine Hn.step rfl ?_
    intro _ x hx
    simp only [proposed, sendMsgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact .inl hx
    · right
      apply selfAck_trOk id _ (by show uint.Z s.term < _; omega)
      have : uint.Z (logLast (logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))))) =
          plogLastIndexZ (toPState s).base (toPState s).log + ents.length := by
        have hB' := hB
        simp only [plogLastIndexZ, toPState, List.length_append] at hB' ⊢
        simp only [logLast, logAppend, List.length_append, List.length_mapIdx]
        rw [hb] at hB'
        have := uint_Z_nonneg s.logst.prev.index'
        push_cast
        rw [show uint.Z s.logst.prev.index' + (s.logst.sents.length : Int) +
          ((s.logst.uents.length : Int) + (ents.length : Int)) =
          uint.Z s.logst.prev.index' + ((s.logst.sents.length : Int) + (s.logst.uents.length : Int)) +
          (ents.length : Int) by omega]
        word
      rw [this]; exact hB
  cases md with
  | static =>
    simp only [ghostRestM]
    iexact Hm
  | dyn dec c0 h0 g =>
    simp only [ghostRestM]
    icases Hm with ⟨%Hd, #HM, #Hfr⟩
    iframe HM Hfr
    ipureintro
    obtain ⟨HD, hc, HI⟩ := Hd
    refine ⟨HD, hc, ?_⟩
    have hrr : (rOf s g).p.role = .leader := hrole'
    have Hpb : propBatch (rOf s g) ents cs = (ents, pciR s) :=
      propConf_noConf' _ _ _ _ ents cs hct hnc
    have H := RInv_propose (dec := effDec dec g.decs) (c0 := c0) id { selfAck id s with entries := ents } cs
      [pselfAck id (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))]
      HI hrr hct (by show plogLastIndexZ (toPState s).base (toPState s).log + (ents.length : Int) < _; omega)
    rw [show ({ selfAck id s with entries := ents } : Msg).entries = ents from rfl, Hpb] at H
    have Hr : rOf (proposed id s ents) g = { rOf s g with
        p := psendMsgs (pappend (rOf s g).p (ents.mapIdx (stamp (rOf s g).p.term (plastIndex (rOf s g).p))))
          [pselfAck id (pappend (toPState s) (ents.mapIdx (stamp s.term (plastIndex (toPState s)))))]
        pci := pciR s } := by
      unfold rOf
      rw [toPState_proposed']
      simp [pciR, proposed, sendMsgs, logAppend]
      exact ⟨rfl, rfl⟩
    rw [Hr]; exact H

end ghostProp

end EtcdGrove
end Perennial
