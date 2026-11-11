/-
Lean-first (no Rocq counterpart). **A `Ready`'s line, in either mode** (2026-11-11, trace-check Q8 stage 1
slice 28n; `notes/decisions.md`, "Q8 stage 1 (slice 28n)"). Raft-internal (not on `etc/api/raft.txt`).

`RawNode.acceptReady` ends with `traceReady(r)`, the node's `Ready` line. Its spec is one for both
modes since slice 28n: here, what its proof gives `traceReady.spec` and gets back.

- `rnTrace_fireReady`: the event builder's gate `TraceFire` of the `Ready` event, from the node's
  capability (`rnTrace`, idle at the cut state `s`, whose outbox the `Ready` handed out), whose update
  leaves the capability idle at the accepted state `s'` (outbox empty: `PhaseStepReady` from
  `SimIdle C s` to `SimIdle C s'`, `SimServerR` not reading `durable`) and gives one token per queued
  message (`readyTok`: `trCap_fire_ready`'s tokens over the queues, `readyToks_queues`). Untraced: the
  nil logger and nothing.
- `readyToks_split`: those tokens split between the self-addressed messages `acceptReady` queues for
  `Advance` (`selfTok`, at no entries and no context: `AAMsgOk`) and the handed-out ones (`MsSub`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedReadyToks
public import Proof.go_etcd_io.raft.v3.TracedHooksGlobal
public import Proof.go_etcd_io.raft.v3.TracedHooks
public import Proof.go_etcd_io.raft.v3.TracedFamilies
public import Proof.go_etcd_io.raft.v3.LemmasReadyR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ready
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The capability, open at a traced node** (`TracedRawNode.lean`'s `rnTrace_some`, which imports
this module's importers). -/
theorem rnTrace_traced (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (s : NState) (γd : GName)
    (h : s.gh.tr = some γd) :
    rnTrace (GF := GF) γ r id c s ⊣⊢
      ⌜s.prevote = false ∧ c.learners = ∅⌝ ∗ r.[raft, go!"checkQuorum"] ↦□ false ∗
        TrNoSnap (some γd) s.logst ∗ ∃ b : Bool, trCapB (some γd) γ r id c b (fun C => SimIdle C s) := by
  unfold rnTrace
  rw [h]
  exact .rfl

/-- **The node's numbers from raft's ghost state, when a condition holds** (`ownRaftGhost_traceBound`
under `P`: a traced cluster, whose receipts fit the trace's bound). -/
theorem ownRaftGhost_traceBoundIf (γ : RaftNames) (id : w64) (p : PState) {md : Bool} (P : Prop)
    (Hfit : P → receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    ⊢ ownRaftGhost (GF := GF) γ id p md ==∗
      ⌜P → plogLastIndexZ p.base p.log < traceNumBound ∧ uint.Z p.commit < traceNumBound⌝ ∗
      ownRaftGhost γ id p md := by
  by_cases hP : P
  · iintro Hg
    imod ownRaftGhost_traceBound (GF := GF) γ id p (Hfit hP) $$ Hg with ⟨%Hb, Hg⟩
    imodintro
    iframe Hg
    ipureintro; exact fun _ => Hb
  · iintro Hg
    imodintro
    iframe Hg
    ipureintro; exact fun h => absurd h hP

/-- **A `Ready` line's phase step**: from the idle phase at the cut state `s` to the idle phase at the
accepted state `s'`, which the protocol reads as `s` but for the outbox (handed out) and the read
states. -/
theorem phaseStepReady_idle (id : w64) (c : CfgM) (s s' : NState) (r' : RdState)
    (hps : toPState s' = { toPState s with outbox := [], rd := r' })
    (ht : s'.term = s.term) (hc : s'.logst.committed = s.logst.committed) :
    PhaseStepReady id c (NodeEvOf (W64 8) id s' c) (fun C => SimIdle C s) (fun C => SimIdle C s') := by
  intro C cs P hΦ hC e he
  refine ⟨⟨s', c, he, hC.2.1⟩, fun a ha => ?_⟩
  obtain ⟨a0, ha0, hR, hL, -, h1, h2, h3⟩ := hΦ
  refine ⟨{ a with durable := Etcdraft.durableOf a }, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hps]
    have h := simServerR_toC (y := a) (ha0.trans ha.symm) hR
    exact h
  · rw [hps]; exact hL
  · rw [hps]; rfl
  · rw [ht]; exact h1
  · rw [hc]; exact h2
  · rw [hps]; exact h3

/-- **The `Ready` line's gate, in either mode** (see the file header). `tl` is the struct's logger
field (`ownRaftPhysReady`'s `Hf_traceLogger`, at its mode's contract); `hb` the event's numbers
within the trace's bound at a traced node. -/
theorem rnTrace_fireReady (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (s s' : NState) (r' : RdState)
    (ms1 ms2 : List QMsg) (tl : GoInterface)
    (hg : s.gh.tr = γ.reTrace) (htr : s'.gh.tr = s.gh.tr) (hpv : s'.prevote = s.prevote)
    (hp : s'.logst.prev = s.logst.prev) (hst : s'.logst.storage = s.logst.storage)
    (hps : toPState s' = { toPState s with outbox := [], rd := r' })
    (ht : s'.term = s.term) (hc : s'.logst.committed = s.logst.committed)
    (hrel : outboxRelP s.outbox ms1 ms2)
    (hb : s.gh.tr ≠ none → uint.nat s'.term < traceNumBound ∧
      uint.nat s'.logst.committed < traceNumBound ∧ uint.nat (plastIndex (toPState s')) < traceNumBound) :
    ⊢ r.[raft, go!"traceLogger"] ↦□ tl -∗ ⌜TraceLoggerOkS s.gh.tr tl⌝ -∗ rnTrace (GF := GF) γ r id c s -∗
      TraceFire s'.gh.tr tl (NodeEvOf (W64 8) id s' c)
        iprop(rnTrace γ r id c s' ∗ [∗list] q ∈ ms1 ++ ms2, readyTok γ q.st) := by
  rw [htr]
  cases htr0 : s.gh.tr with
  | none =>
    iintro #Htl %Hok Htr
    iapply (traceFire_none tl _ _).2
    isplitr
    · ipureintro; exact Hok
    isplitr
    · iapply rnTrace_none γ r id c s' (htr.trans htr0)
    · iapply readyToks_none γ QMsg.st (ms1 ++ ms2) (hg ▸ htr0)
  | some γd =>
    have hγ : γ.reTrace = some γd := hg ▸ htr0
    obtain ⟨hTn, hCn, hLn⟩ := hb (by rw [htr0]; exact Option.some_ne_none γd)
    iintro #Htl %- Htr
    icases (rnTrace_traced γ r id c s γd htr0).1 $$ Htr with ⟨%Hpv, #Hcq, #Hns, %b, Hcap⟩
    have hfire := trCap_fire_ready (GF := GF) γd γ r id c tl (NodeEvOf (W64 8) id s' c)
      (fun C => SimIdle C s) (fun C => SimIdle C s') (fun _ => True) (fun _ => True)
      (phaseStepReady_idle id c s s' r' hps ht hc) (fun _ _ => trivial)
      (fun e he => nodeEvOf_ok (W64 8) id s' c e _ he (by decide) hTn hCn hLn (Nat.le_refl _))
    iapply traceFire_mono (some γd) tl (NodeEvOf (W64 8) id s' c)
      iprop(trCapB (some γd) γ r id c true (fun C => SimIdle C s') (fun _ => True) ∗
        ∃ (tn : TraceNames) (P : List Etcdraft.Msg) (Bn : GMap Nat Etcdraft.Msg), traceDir γd tn ∗
          ⌜∃ cs, SimIdle tn.voters s cs P⌝ ∗ ⌜((GMap.toList Bn).map Prod.snd).Perm P⌝ ∗
          [∗map] k ↦ m ∈ Bn, inFlight tn k m) _
    isplitr [Hcap]
    · iintro ⟨Hcap', %tn, %P, %Bn, #Hdir, %HP, %HB, Hbn⟩
      obtain ⟨cs, hcs⟩ := HP
      have hP : P = pendAbs tn.voters s.outbox := ((simIdle_iff _ s cs P).1 hcs).2
      isplitl [Hcap']
      · iapply (rnTrace_traced γ r id c s' γd (htr.trans htr0)).2
        isplitr
        · ipureintro; rw [hpv]; exact Hpv
        iframe Hcq
        isplitr
        · unfold TrNoSnap; rw [hp, hst]; iexact Hns
        iexists true
        iexact Hcap'
      · ihave H := readyToks_queues γd tn Bn P HB s.outbox ms1 ms2 hP hrel $$ Hdir Hbn
        simp only [readyTok, hγ]
        iexact H
    · iapply hfire
      iframe Htl
      iunfold trCap
      iexists b
      iexact Hcap

/-- A self-addressed message's token, from its `readyTok` (no entries, no context). -/
theorem selfToks_of_readyToks (γ : RaftNames) :
    ∀ (l : List QMsg), (∀ q ∈ l, q.st.ents = [] ∧ q.st.ctx = []) →
    ([∗list] q ∈ l, readyTok (GF := GF) γ q.st) ⊢ [∗list] q ∈ l, selfTok γ q.st := by
  intro l
  induction l with
  | nil => intro _; iintro _; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons q qs ih =>
    intro hl
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hq, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hq]
    · obtain ⟨he, hx⟩ := hl q List.mem_cons_self
      unfold readyTok selfTok
      cases γ.reTrace with
      | none => itrivial
      | some γd => iExactEq Hq; rw [he, hx]
    · iapply ih (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')) $$ H

/-- **The tokens of the queues, split** between the self-addressed messages `acceptReady` keeps for
`Advance` (`selfTok`, at no entries and no context) and the handed-out ones. -/
theorem readyToks_selfSplit (γ : RaftNames) (id : w64) (ms ms1 ms2 : List QMsg) (hsub : MsSub id ms ms1 ms2)
    (hself : ∀ q ∈ ms2, q.st.msg.To' = id → q.st.ents = [] ∧ q.st.ctx = []) :
    ([∗list] q ∈ ms1 ++ ms2, readyTok (GF := GF) γ q.st) ⊢
      ([∗list] q ∈ selfmsgs id ms2, selfTok γ q.st) ∗ [∗list] q ∈ ms, readyTok γ q.st := by
  obtain ⟨l, hlp, hls⟩ := hsub
  obtain ⟨r0, hr0⟩ := hls.exists_perm_append
  iintro H
  ihave H := (BigSepL.bigSepL_perm (Φ := fun q : QMsg => readyTok (GF := GF) γ q.st) hr0).1 $$ H
  ihave H := BigSepL.bigSepL_submseteq (Φ := fun q : QMsg => readyTok (GF := GF) γ q.st)
    (l₁ := l) (l := r0) (List.Perm.refl _) $$ H
  ihave H := (BigSepL.bigSepL_perm (Φ := fun q : QMsg => readyTok (GF := GF) γ q.st) hlp).1 $$ H
  icases (BigSepL.bigSepL_append (Φ := fun (_ : Nat) (q : QMsg) => readyTok (GF := GF) γ q.st)
    (l₁ := ms) (l₂ := ms2.filter (fun q => isSelfQ id q))).1 $$ H with ⟨Hm, Hs⟩
  iframe Hm
  have hsel : ∀ q ∈ selfmsgs id ms2, q.st.ents = [] ∧ q.st.ctx = [] := by
    intro q hq
    obtain ⟨hq2, hto⟩ := List.mem_filter.1 hq
    exact hself q hq2 (of_decide_eq_true hto)
  iapply selfToks_of_readyToks γ _ hsel $$ Hs

end ready

end EtcdGrove
end Perennial
