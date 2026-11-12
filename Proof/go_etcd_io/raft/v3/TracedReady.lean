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
theorem rnTrace_traced (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (dl : List EntryM) (s : NState)
    (γd : GName) (h : s.gh.tr = some γd) :
    rnTrace (GF := GF) γ r id c dl s ⊣⊢
      ⌜s.prevote = false ∧ c.learners = ∅⌝ ∗ ⌜RnTrPure γ c s⌝ ∗ r.[raft, go!"checkQuorum"] ↦□ false ∗
        TrNoSnap (some γd) s.logst ∗ ∃ b : Bool, ⌜dl ≠ [] → b = true⌝ ∗
          trCapB (some γd) γ r id c b (fun C => SimIdle C s) := by
  unfold rnTrace
  rw [h]
  exact .rfl

/-! ### The handed-out messages' types (2026-11-12, trace-check implementation step 3; design §3.6) -/

section types
omit [GooseSemantics] [GooseInterp] go_gctx [StorageModel GF] sem package_sem

theorem mtypeOf_eq_app {t : w32} (H : mtypeOf t = some .app) : t = MsgApp := by
  unfold mtypeOf at H; split at H <;> simp_all; rename_i h; exact uint_Z_inj.1 (by rw [h]; rfl)
theorem mtypeOf_eq_appResp {t : w32} (H : mtypeOf t = some .appResp) : t = MsgAppResp := by
  unfold mtypeOf at H; split at H <;> simp_all; rename_i h; exact uint_Z_inj.1 (by rw [h]; rfl)
theorem mtypeOf_eq_vote {t : w32} (H : mtypeOf t = some .vote) : t = MsgVote := by
  unfold mtypeOf at H; split at H <;> simp_all; rename_i h; exact uint_Z_inj.1 (by rw [h]; rfl)
theorem mtypeOf_eq_voteResp {t : w32} (H : mtypeOf t = some .voteResp) : t = MsgVoteResp := by
  unfold mtypeOf at H; split at H <;> simp_all; rename_i h; exact uint_Z_inj.1 (by rw [h]; rfl)
theorem mtypeOf_eq_heartbeat {t : w32} (H : mtypeOf t = some .heartbeat) : t = MsgHeartbeat := by
  unfold mtypeOf at H; split at H <;> simp_all; rename_i h; exact uint_Z_inj.1 (by rw [h]; rfl)
theorem mtypeOf_eq_heartbeatResp {t : w32} (H : mtypeOf t = some .heartbeatResp) :
    t = MsgHeartbeatResp := by
  unfold mtypeOf at H; split at H <;> simp_all; rename_i h; exact uint_Z_inj.1 (by rw [h]; rfl)
theorem mtypeOf_eq_propose {t : w32} (H : mtypeOf t = some .propose) : t = MsgProp := by
  unfold mtypeOf at H; split at H <;> simp_all; rename_i h; exact uint_Z_inj.1 (by rw [h]; rfl)

/-- A described type the trace logs is a traced network type. -/
theorem mtypeOf_traced_trNetTy {t : w32} {ty : MsgType} (h : mtypeOf t = some ty)
    (ht : ty.traced = true) : TrNetTy t := by
  unfold TrNetTy
  cases ty <;> simp [MsgType.traced] at ht <;> first
  | exact .inl (mtypeOf_eq_app h)
  | exact .inr (.inl (mtypeOf_eq_appResp h))
  | exact .inr (.inr (.inl (mtypeOf_eq_vote h)))
  | exact .inr (.inr (.inr (.inl (mtypeOf_eq_voteResp h))))
  | exact .inr (.inr (.inr (.inr (.inl (mtypeOf_eq_heartbeat h)))))
  | exact .inr (.inr (.inr (.inr (.inr (mtypeOf_eq_heartbeatResp h)))))

/-- **A queued message's type, from its abstraction**: of a described type (`XfOk`'s traced clause),
its abstraction (if any) a `TrOutMsg` (`rnTrace`'s clause (b) on the outbox): a type a traced node
hands out (`TrSent`). -/
theorem trSent_of_abs {st : MsgSt} {a : Option Msg} (ha : msgAbs st a)
    (hty : mtypeOf st.msg.Type' ≠ none) (hx : ∀ x, a = some x → TrOutMsg x) : TrSent st := by
  rcases ha with ⟨h1, -⟩ | ⟨ty, h1, -, rfl⟩ | ⟨sv, h1, -, rfl⟩
  · exact absurd h1 hty
  · rcases hx _ rfl with h | ⟨h, hents⟩
    · simp only [absMsg, absMsgFrom] at h
      exact .inl (mtypeOf_traced_trNetTy h1 h)
    · simp only [absMsg, absMsgFrom] at h hents
      subst h
      exact .inr ⟨mtypeOf_eq_propose h1, fun e he => hents e he⟩
  · rcases hx _ rfl with h | ⟨h, -⟩ <;> simp [absSnap, absSnapFrom, MsgType.traced] at h

theorem forall₂_msgAbs_mem {ms : List QMsg} {as_ : List (Option Msg)}
    (h : List.Forall₂ (fun q a => msgAbs q.st a) ms as_) : ∀ q ∈ ms, ∃ a ∈ as_, msgAbs q.st a := by
  induction h with
  | nil => intro q hq; cases hq
  | cons hqa _ ih =>
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨_, List.mem_cons_self, hqa⟩
    · obtain ⟨a, ha, h⟩ := ih q hq
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

/-- **Every queued message a type a traced node hands out** (`TrSent`), from the queues' relation to
the outbox, the outbox's `TrOutMsg`s and the queued messages' described types. -/
theorem outboxRelP_trSent {o : List Msg} {ms1 ms2 : List QMsg} (h : outboxRelP o ms1 ms2)
    (hout : ∀ m ∈ o, TrOutMsg m) (hty : ∀ q ∈ ms1 ++ ms2, mtypeOf q.st.msg.Type' ≠ none) :
    ∀ q ∈ ms1 ++ ms2, TrSent q.st := by
  obtain ⟨as1, as2, hp, h1, h2⟩ := h
  intro q hq
  have key : ∃ a, msgAbs q.st a ∧ ∀ x, a = some x → x ∈ o := by
    rcases List.mem_append.1 hq with hq' | hq'
    · obtain ⟨a, ha, hab⟩ := forall₂_msgAbs_mem h1 q hq'
      refine ⟨a, hab, fun x hx => hp.mem_iff.2 (List.mem_append_left _ ?_)⟩
      exact List.mem_filterMap.2 ⟨a, ha, by rw [hx]; rfl⟩
    · obtain ⟨a, ha, hab⟩ := forall₂_msgAbs_mem h2 q hq'
      refine ⟨a, hab, fun x hx => hp.mem_iff.2 (List.mem_append_right _ ?_)⟩
      exact List.mem_filterMap.2 ⟨a, ha, by rw [hx]; rfl⟩
  obtain ⟨a, ha, hin⟩ := key
  exact trSent_of_abs ha (hty q hq) (fun x hx => hout x (hin x hx))

end types

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

/-- (2026-11-12, trace-check step 4) The capability's trace directory, with the node among its
voters (for the handed-out append responses' `trFromOk`). -/
theorem trCapB_dirId (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    trCapB (GF := GF) (some γd) γ r id c b Φ Λ ⊢
      (∃ tn : TraceNames, traceDir γd tn ∗ ⌜id ∈ tn.voters⌝) ∗ trCapB (some γd) γ r id c b Φ Λ := by
  apply persistent_entails_right
  iintro H
  iunfold trCapB at H
  icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, -⟩
  iexists tn
  iframe Hdir
  ipureintro
  rw [Hpf.1]; exact Hpf.2.2.2.1

/-- **The `Ready` line's gate, in either mode** (see the file header). `tl` is the struct's logger
field (`ownRaftPhysReady`'s `Hf_traceLogger`, at its mode's contract); `hb` the event's numbers
within the trace's bound at a traced node. -/
theorem rnTrace_fireReady (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) {dl dl' : List EntryM}
    (s s' : NState) (r' : RdState)
    (ms1 ms2 : List QMsg) (tl : GoInterface)
    (hg : s.gh.tr = γ.reTrace) (htr : s'.gh.tr = s.gh.tr) (hpv : s'.prevote = s.prevote)
    (hp : s'.logst.prev = s.logst.prev) (hst : s'.logst.storage = s.logst.storage)
    (hps : toPState s' = { toPState s with outbox := [], rd := r' })
    (ht : s'.term = s.term) (hc : s'.logst.committed = s.logst.committed)
    (hrel : outboxRelP s.outbox ms1 ms2)
    (hb : s.gh.tr ≠ none → uint.nat s'.term < traceNumBound ∧
      uint.nat s'.logst.committed < traceNumBound ∧ uint.nat (plastIndex (toPState s')) < traceNumBound)
    -- (2026-11-12, trace-check implementation step 3) the scope's fields kept (`rnTrace`'s (b)), and
    -- every queued message of a described type (`XfOk`'s traced clause), for `readyTok`'s `TrSent`
    (hlt : s'.lt = s.lt) (hro : s'.rd.ro.pending = s.rd.ro.pending) (hpd : s'.rd.pend = s.rd.pend)
    (hrole : s'.role = s.role) (hap : s'.logst.applied = s.logst.applied)
    (hxty : s.gh.tr.isSome → ∀ q ∈ ms1 ++ ms2, mtypeOf q.st.msg.Type' ≠ none)
    -- (2026-11-12, trace-check step 4) every queued append response from the node (`QOk`), for the
    -- tokens' `trFromOk`
    (hfrom : ∀ q ∈ ms1 ++ ms2, q.st.msg.Type' = MsgAppResp → q.st.msg.From' = id) :
    ⊢ r.[raft, go!"traceLogger"] ↦□ tl -∗ ⌜TraceLoggerOkS s.gh.tr tl⌝ -∗ rnTrace (GF := GF) γ r id c dl s -∗
      TraceFire s'.gh.tr tl (NodeEvOf (W64 8) id s' c)
        iprop(rnTrace γ r id c dl' s' ∗ [∗list] q ∈ ms1 ++ ms2, readyTok γ q.st) := by
  rw [htr]
  cases htr0 : s.gh.tr with
  | none =>
    iintro #Htl %Hok Htr
    iapply (traceFire_none tl _ _).2
    isplitr
    · ipureintro; exact Hok
    isplitr
    · iapply rnTrace_none γ r id c dl' s' (htr.trans htr0)
    · iapply readyToks_none γ QMsg.st (ms1 ++ ms2) (hg ▸ htr0)
  | some γd =>
    have hγ : γ.reTrace = some γd := hg ▸ htr0
    obtain ⟨hTn, hCn, hLn⟩ := hb (by rw [htr0]; exact Option.some_ne_none γd)
    iintro #Htl %- Htr
    icases (rnTrace_traced γ r id c dl s γd htr0).1 $$ Htr with ⟨%Hpv, %Hpure, #Hcq, #Hns, %b, %-, Hcap⟩
    icases trCapB_dirId γd γ r id c b _ _ $$ Hcap with ⟨⟨%tn0, #Hdir0, %Hid0⟩, Hcap⟩
    have hsent : ∀ q ∈ ms1 ++ ms2, TrSent q.st :=
      outboxRelP_trSent hrel Hpure.2.1 (hxty (by rw [htr0]; rfl))
    have Hpure' : RnTrPure γ c s' := by
      have ho : s'.outbox = [] := congrArg PState.outbox hps
      refine ⟨⟨hlt.trans Hpure.1.1, hro.trans Hpure.1.2.1, hpd.trans Hpure.1.2.2⟩, ?_, Hpure.2.2.1,
        Hpure.2.2.2.keep hrole (by rw [hap]; exact Int.le_refl _)⟩
      rw [ho]; intro m hm; cases hm
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
      · iapply (rnTrace_traced γ r id c dl' s' γd (htr.trans htr0)).2
        isplitr
        · ipureintro; rw [hpv]; exact Hpv
        isplitr
        · ipureintro; exact Hpure'
        iframe Hcq
        isplitr
        · unfold TrNoSnap; rw [hp, hst]; iexact Hns
        iexists true
        isplitr
        · ipureintro; exact fun _ => rfl
        iexact Hcap'
      · ihave H := readyToks_queues γd tn Bn P HB s.outbox ms1 ms2 hP hrel $$ Hdir Hbn
        simp only [readyTok, hγ]
        ihave H := bigSepL_pure_and (fun q : QMsg => TrSent q.st)
          (fun q : QMsg => recvTokOf (GF := GF) γd q.st.msg q.st.ents q.st.ctx) _ hsent $$ H
        ihave H := bigSepL_sep_addR
          (fun q : QMsg => iprop(⌜TrSent q.st⌝ ∗ recvTokOf (GF := GF) γd q.st.msg q.st.ents q.st.ctx))
          (fun q : QMsg => trFromOk (GF := GF) γd q.st) (traceDir γd tn0) (ms1 ++ ms2)
          (fun q hq => by
            iintro #Hd
            iunfold trFromOk
            iexists tn0
            iframe Hd
            ipureintro
            intro h; rw [hfrom q hq h]; exact Hid0) $$ Hdir0 H
        have hassoc : ([∗list] q ∈ ms1 ++ ms2, iprop((⌜TrSent q.st⌝ ∗
            recvTokOf (GF := GF) γd q.st.msg q.st.ents q.st.ctx) ∗ trFromOk γd q.st)) ⊢
            [∗list] q ∈ ms1 ++ ms2, iprop(⌜TrSent q.st⌝ ∗
              recvTokOf (GF := GF) γd q.st.msg q.st.ents q.st.ctx ∗ trFromOk γd q.st) := by
          apply BigSepL.bigSepL_mono
          intro k x _
          iintro ⟨⟨%h, A⟩, B⟩
          iframe A B
          ipureintro; exact h
        iapply hassoc $$ H
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
      | some γd => icases Hq with ⟨-, Hq, -⟩; iExactEq Hq; rw [he, hx]
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
