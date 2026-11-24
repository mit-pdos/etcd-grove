/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2/Laws.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Stage 2's invariant's laws that need no prophecy or connection resources (statements; proofs in
Prove): the trace and prediction witnesses, the receive tokens (`recv_msg`), and the step
results' facts a handler needs to refute its dead branches (`step_ok_msg`, `step_ok_free`, from
the pure layer's totality) and the free events' `.ok` per kind (`step_ok_req`, `step_ok_recover`,
`step_ok_exec`). The replica's step itself (`replica_step`), the prophecy's laws and the
request tokens are in `Proto2/Replica.lean`.
-/
module

public import Dsverify.Proof.gryff.Proto2.InvDefs
public import Dsverify.Proof.gryff.Pure.Totality
public import Dsverify.Proof.gryff.Proto2P.Ghost
public import Dsverify.Proof.gryff.Proto2P.Facts
import Dsverify.Proof.gryff.PureP.Stable

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto
open model kahn pure p2

section
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

/-! ## Witnesses -/

theorem traceHalf_lb (γ : ProtoNames) (k : Fin 3) (t : List Ev) :
    traceHalf (GF := GF) γ k t ⊢ |==> traceHalf γ k t ∗ traceLb γ k t := by
  unfold traceHalf traceLb
  refine (persistent_entails_left (monoListLbOwn_get _ _ _)).trans ?_
  iintro ⟨H, #Hlb⟩
  iframe Hlb
  imodintro
  iexact H

theorem traceHalf_lb_prefix (γ : ProtoNames) (k : Fin 3) (t t' : List Ev) :
    traceHalf (GF := GF) γ k t ∗ traceLb γ k t' ⊢ ⌜t' <+: t⌝ := by
  unfold traceHalf traceLb
  iintro ⟨H1, H2⟩
  ihave %h := mono_list_auth_lb_valid (GF := GF) _ _ _ _ $$ H1 H2
  ipureintro; exact h.2

theorem predIs_agree (γ : ProtoNames) (n : Nat) (ws ws' : List w64) :
    predIs (GF := GF) γ n ws ∗ predIs γ n ws' ⊢ ⌜ws = ws'⌝ := by
  unfold predIs
  iintro ⟨H1, H2⟩
  ihave %h := ghostMapElem_agree $$ H1 H2
  ipureintro; exact Option.some.inj h

theorem predIdIs_agree (γ : ProtoNames) (i : Nat) (ws ws' : List w64) :
    predIdIs (GF := GF) γ i ws ∗ predIdIs γ i ws' ⊢ ⌜ws = ws'⌝ := by
  unfold predIdIs
  iintro ⟨H1, H2⟩
  ihave %h := ghostMapElem_agree $$ H1 H2
  ipureintro; exact Option.some.inj h

theorem predsSet_intro (γ : ProtoNames) (ws0 ws1 ws2 : List w64) :
    predIdIs (GF := GF) γ 0 ws0 ∗ predIdIs γ 1 ws1 ∗ predIdIs γ 2 ws2 ⊢ predsSet γ := by
  unfold predsSet
  iintro ⟨H0, H1, H2⟩
  iexists ws0, ws1, ws2
  iframe H0 H1 H2

/-- **The registration of a prediction** (D13; the master, under its lock, registering replica
node `n` as replica id `i`, with the registry's `nodeIdIs`): replica id `i`'s slot takes node `n`'s
recorded prediction. Sound because no replica steps before all three are set (`unset`), and a
replica id's prediction is its node's (`predNode`). -/
theorem pred_register (γ : ProtoNames) (n i : Nat) (ws : List w64) (hi : i < 3) (E : CoPset)
    (hE : ↑gryffN ⊆ E) :
    gryffInv2 (GF := GF) γ ∗ predSlot γ i ∗ predIs γ n ws ∗ nodeIdIs γ n (W64 i) ⊢
      |={E}=> predIdIs γ i ws := by
  iintro ⟨#Hinv, Hslot, #Hpn, Hnid⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod HP; imod HNP
  iunfold predSlot at Hslot
  iunfold predIs at Hpn
  ihave %hP := ghost_map_lookup $$ HP Hslot
  ihave %hNP := ghost_map_lookup $$ HNP Hpn
  imod ghost_map_update (some ws) $$ HP Hslot with ⟨HP, Hel⟩
  imod ghostMapElem_persist $$ Hel with #Hel
  let Φ : Option Nat → Nat → IProp GF := fun o j =>
    gryffInv2Body.match_1 (fun _ => IProp GF) o (fun n => nodeIdIs γ n (W64 j)) (fun _ => iprop(True))
  have eΦ : Φ (some n) i = nodeIdIs γ n (W64 i) := rfl
  ihave Hids := BI.later_mono (ids_update Φ S.idNode i n hi) $$ [Hids Hnid]
  · inext
    isplitl [Hids]
    · iexact Hids
    · rw [eΦ]; iexact Hnid
  imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
    Hcur Hrx Hreqs Hres] with -
  · inext
    iexists { S with P := S.P.insert i (some ws), idNode := S.idNode.insert i n }
    iframe
    ipureintro
    exact facts_pred_register Hf hi hP hNP
  imodintro
  unfold predIdIs
  iexact Hel

theorem streamLb_prefix (γ : ProtoNames) (k q : Fin 3) (ms ms' : List Msg) (h : ms' <+: ms) :
    streamLb (GF := GF) γ k q ms ⊢ streamLb γ k q ms' := by
  unfold streamLb
  iintro ⟨%t, H, %hp⟩
  iexists t
  iframe H
  ipureintro; exact h.trans hp

/-- The sender's own stream, from its trace's lower bound. -/
theorem streamLb_intro (γ : ProtoNames) (k q : Fin 3) (t : List Ev) :
    traceLb (GF := GF) γ k t ⊢ streamLb γ k q (streamOf k q t) := by
  unfold streamLb
  iintro H
  iexists t
  iframe H
  ipureintro; exact List.prefix_refl _

/-! ## Receive tokens -/

/-- **Receive** (a listener of `q` reading `k`'s `n`-th message; for `k = q`, replica `k`'s own
send to itself, under its lock): with the cursor at `n` and the stream's first `n + 1` messages,
the token of message `n`. -/
theorem recv_msg (γ : ProtoNames) (k q : Fin 3) (n : Nat) (ms : List Msg) (m : Msg) (E : CoPset)
    (hE : ↑gryffN ⊆ E) (hn : ms.length = n) :
    gryffInv2 (GF := GF) γ ∗ rxCurTok γ k q n ∗ streamLb γ k q (ms ++ [m]) ⊢
      |={E}=> rxCurTok γ k q (n + 1) ∗ rxTok γ k q n m := by
  iintro ⟨#Hinv, Hc, #Hlb⟩
  unfold streamLb
  icases Hlb with ⟨%t0, #Htlb, %hpre⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Ht0; imod Ht1; imod Ht2; imod Hcur; imod Hrx
  ihave Htr3 : traces3 (GF := GF) γ S.T $$ [Ht0 Ht1 Ht2]
  · unfold traces3; iframe Ht0 Ht1 Ht2
  ihave %ht0 := traces3_lb (GF := GF) γ S.T k t0 $$ Htr3 Htlb
  unfold rxCurTok
  ihave %hcur := ghost_map_lookup $$ Hcur Hc
  obtain ⟨c, hc, hrun⟩ := real_run Hf
  have hm : (streamOf k q (S.T k))[n]? = some m := by
    obtain ⟨u, hu⟩ := (hpre.trans (streamOf_prefix (hrun k) ht0 q))
    rw [← hu, List.getElem?_append_left (by simp [hn]), List.getElem?_append_right (by omega)]
    simp [hn]
  obtain ⟨hnone, hf'⟩ := facts_recv Hf hcur hm
  imod ghost_map_update (n + 1) $$ Hcur Hc with ⟨Hcur, Hc⟩
  imod ghost_map_insert (k.val, q.val, n) m hnone $$ Hrx with ⟨Hrx, Hm⟩
  iunfold traces3 at Htr3
  icases Htr3 with ⟨Ht0, Ht1, Ht2⟩
  imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
    Hcur Hrx Hreqs Hres] with -
  · inext
    iexists { S with cur := S.cur.insert (k.val, q.val) (n + 1), rx := S.rx.insert (k.val, q.val, n) m }
    iframe
    ipureintro; exact hf'
  imodintro
  unfold rxTok
  iframe Hc Hm

/-! ## Step results (totality) -/

/-- A message whose receive token replica `k` holds is handled: its step is `.ok` (the pure
layer's `total_msg`: the message is in flight in the real configuration). The handler refutes its
dead branches with it. -/
theorem step_ok_msg (γ : ProtoNames) (k k' : Fin 3) (t : List Ev) (n : Nat) (m : Msg) (E : CoPset)
    (hE : ↑gryffN ⊆ E) :
    gryffInv2 (GF := GF) γ ∗ traceHalf γ k t ∗ rxTok γ k' k n m ⊢
      |={E}=> traceHalf γ k t ∗ rxTok γ k' k n m ∗
        ⌜∃ s' o, stepR k (stOf k t) (.msg m) = .ok (s', o)⌝ := by
  iintro ⟨#Hinv, Htr, Htok⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Ht0; imod Ht1; imod Ht2; imod Hrx
  ihave Htr3 : traces3 (GF := GF) γ S.T $$ [Ht0 Ht1 Ht2]
  · unfold traces3; iframe Ht0 Ht1 Ht2
  ihave %hT := traces3_agree' (GF := GF) γ S.T k t $$ Htr3 Htr
  unfold rxTok
  ihave %hl := ghost_map_lookup $$ Hrx Htok
  obtain ⟨c, hc⟩ := Hf.run
  have hin := real_inflight Hf hc (token_count_lt' Hf hl)
  obtain ⟨s', o, ho⟩ := total_msg hc k m hin
  rw [← real_stOf Hf hc k, hT] at ho
  iunfold traces3 at Htr3
  icases Htr3 with ⟨Ht0, Ht1, Ht2⟩
  imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
    Hcur Hrx Hreqs Hres] with -
  · inext
    iexists S
    iframe
    ipureintro; exact Hf
  imodintro
  iframe Htr Htok
  ipureintro; exact ⟨s', o, ho⟩

/-- A free event of the system's shape at replica `k` (a client request with its token, a timer,
a recovery trigger, an execution): its step is neither `never` nor `dead` (`total_free`), and a
client request's key is fresh at `k` (from its token: the key guard), and `k` has handled fewer
than 24 client requests (the budget: D14, the invariant's `reqBudget`). The remaining guards (the
recovery trigger's `i < crt q`, the execution's `execGuard`) are the handler's to show from the
replica's state. -/
theorem step_ok_free (γ : ProtoNames) (k : Fin 3) (t : List Ev) (e : Ev) (he : e.recv = none)
    (hp : e.Producible) (E : CoPset) (hE : ↑gryffN ⊆ E) :
    gryffInv2 (GF := GF) γ ∗ traceHalf γ k t ∗ evTok γ k e ⊢
      |={E}=> traceHalf γ k t ∗ evTok γ k e ∗
        ⌜stepR k (stOf k t) e ≠ .error .never ∧ stepR k (stOf k t) e ≠ .error .dead ∧
          ∀ cid rid i, e.clientReq = some (cid, rid, i) →
            (cid, rid) ∉ (stOf k t).used ∧ (stOf k t).nReqs < 24⌝ := by
  iintro ⟨#Hinv, Htr, Htok⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Ht0; imod Ht1; imod Ht2; imod Hreqs
  ihave Htr3 : traces3 (GF := GF) γ S.T $$ [Ht0 Ht1 Ht2]
  · unfold traces3; iframe Ht0 Ht1 Ht2
  ihave %hT := traces3_agree' (GF := GF) γ S.T k t $$ Htr3 Htr
  ihave %htk := evTok_req_lookup (GF := GF) γ k e S.reqs $$ Hreqs Htok
  obtain ⟨c, hc⟩ := Hf.run
  have hst := real_stOf Hf hc k
  rw [hT] at hst
  have hfree := total_free hc k e he hp
  rw [← hst] at hfree
  have hpure : stepR k (stOf k t) e ≠ .error .never ∧ stepR k (stOf k t) e ≠ .error .dead ∧
      ∀ cid rid i, e.clientReq = some (cid, rid, i) →
        (cid, rid) ∉ (stOf k t).used ∧ (stOf k t).nReqs < 24 := by
    refine ⟨?_, ?_, ?_⟩
    · rcases hfree with ⟨s', o, h⟩ | h <;> rw [h] <;> intro h' <;> cases h'
    · rcases hfree with ⟨s', o, h⟩ | h <;> rw [h] <;> intro h' <;> cases h'
    · intro cid rid i hcr
      have htk' := htk cid rid i hcr
      refine ⟨fun hu => ?_, ?_⟩
      · have hr := real_runP Hf hc k
        rw [hT, ← hst] at hr
        have hr' : runP gNet k (projR S.l1 k) = some (stOf k t, outsP k t) := by
          rw [Hf.proj k, hT]; exact hr
        obtain ⟨op, hop, -, h1, h2⟩ := used_ops hr' hu
        exact Hf.reqFresh _ _ htk' op hop (idZ_eq h1 h2)
      · rw [← hT]; exact Hf.reqBudget _ k i htk'
  iunfold traces3 at Htr3
  icases Htr3 with ⟨Ht0, Ht1, Ht2⟩
  imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
    Hcur Hrx Hreqs Hres] with -
  · inext
    iexists S
    iframe
    ipureintro; exact Hf
  imodintro
  iframe Htr Htok
  ipureintro; exact hpure

/-! ### Per kind: the free events' `.ok` (review stage 2, finding 3)

What the run loop's and the executor's cases use, so that no caller unfolds `stepR`: from
`step_ok_free` and the pure guard laws (`Pure/Totality.lean`: `stepReq_ne_disabled`,
`stepRecover_ne_disabled`, `stepExec_ne_disabled`, `stepR_ok_of_ne`). The forced-write ticker
needs no law: `stepR_forceWrite` (`.ok (s, [])` in every state). -/

/-- **A client request** (the run loop's `readChan` / `writeChan` / `rmwChan` cases): with its
token and its shape (`reqChanP`'s `Ev.Producible`), its step is `.ok`. -/
theorem step_ok_req (γ : ProtoNames) (k : Fin 3) (t : List Ev) (e : Ev) {cid rid : w32}
    {i : dsverify_lab.harness.RegInput w64} (hr : e.clientReq = some (cid, rid, i))
    (hp : e.Producible) (E : CoPset) (hE : ↑gryffN ⊆ E) :
    gryffInv2 (GF := GF) γ ∗ traceHalf γ k t ∗ evTok γ k e ⊢
      |={E}=> traceHalf γ k t ∗ evTok γ k e ∗
        ⌜∃ s' o, stepR k (stOf k t) e = .ok (s', o)⌝ := by
  iintro H
  imod step_ok_free γ k t e (recv_of_clientReq hr) hp E hE $$ H with ⟨Htr, Htok, %h⟩
  imodintro
  iframe Htr Htok
  ipureintro
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hu, hb⟩ := h3 cid rid i hr
  exact stepR_ok_of_ne h1 (stepReq_ne_disabled k _ e hr hu hb) h2

/-- **The recovery trigger** `(q, i)` (the run loop's `instancesToRecover` case): with its guard
(`recoverChanP`'s `rowOk q`, `0 ≤ i`, and `i < crtInstance[q]` from `epaxosOwn_crtLb_le`), its
step is `.ok`. -/
theorem step_ok_recover (γ : ProtoNames) (k : Fin 3) (t : List Ev) (q i : w32)
    (hq : rowOk q = true) (h0 : 0 ≤ sint.Z i) (hc : sint.Z i < sint.Z ((stOf k t).crt q))
    (E : CoPset) (hE : ↑gryffN ⊆ E) :
    gryffInv2 (GF := GF) γ ∗ traceHalf γ k t ⊢
      |={E}=> traceHalf γ k t ∗ ⌜∃ s' o, stepR k (stOf k t) (.recover q i) = .ok (s', o)⌝ := by
  iintro ⟨#Hinv, Htr⟩
  have htok : evTok (GF := GF) γ k (.recover q i) = iprop(True) := rfl
  imod step_ok_free γ k t (.recover q i) rfl trivial E hE $$ [Htr] with ⟨Htr, -, %h⟩
  · rw [htok]; iframe Hinv Htr
  imodintro
  iframe Htr
  ipureintro
  exact stepR_ok_of_ne h.1 (stepRecover_ne_disabled k _ q i hq h0 hc) h.2.1

/-- **The execution** of `(q, i)` (`strongconnect`'s loop over a popped component): with its guard
(in the box, its copy committed, `execGuard` from the component: `sccStep`), its step is `.ok`. -/
theorem step_ok_exec (γ : ProtoNames) (k : Fin 3) (t : List Ev) (q i : w32) (c : Copy)
    (hb : inBox q i = true) (hc : (stOf k t).inst q i = some c) (hs : c.status = St.COMMITTED)
    (hg : execGuard (stOf k t) (sint.Z q, sint.Z i)) (E : CoPset) (hE : ↑gryffN ⊆ E) :
    gryffInv2 (GF := GF) γ ∗ traceHalf γ k t ⊢
      |={E}=> traceHalf γ k t ∗ ⌜∃ s' o, stepR k (stOf k t) (.exec q i) = .ok (s', o)⌝ := by
  iintro ⟨#Hinv, Htr⟩
  have htok : evTok (GF := GF) γ k (.exec q i) = iprop(True) := rfl
  imod step_ok_free γ k t (.exec q i) rfl trivial E hE $$ [Htr] with ⟨Htr, -, %h⟩
  · rw [htok]; iframe Hinv Htr
  imodintro
  iframe Htr
  ipureintro
  exact stepR_ok_of_ne h.1 (stepExec_ne_disabled k _ q i c hb hc hs hg) h.2.1

/-! ## The executor's laws (H-X-1, H-X-3) -/

/-- **Stability along a replica's own trace** (H-X-1; the executor across a release of the
lock): a later trace `t'` (the current half) extends a lower bound `t`; every committed or executed
copy at `t` is still one at `t'` with the same commands, `seq`, `deps` and base (a `Commit` to a
committed copy carries the same attributes: agreement); an instance present at `t` is present at
`t'`. -/
theorem trace_stable (γ : ProtoNames) (k : Fin 3) (t t' : List Ev) (E : CoPset)
    (hE : ↑gryffN ⊆ E) :
    gryffInv2 (GF := GF) γ ∗ traceHalf γ k t' ∗ traceLb γ k t ⊢
      |={E}=> traceHalf γ k t' ∗ ⌜t <+: t' ∧
        (∀ n c, committedCopy (stOf k t) n = some c → ∃ c', committedCopy (stOf k t') n = some c' ∧
          c'.cmds = c.cmds ∧ c'.seq = c.seq ∧ c'.deps = c.deps ∧ c'.base = c.base) ∧
        (∀ q i : w32, ((stOf k t).inst q i).isSome → ((stOf k t').inst q i).isSome)⌝ := by
  iintro ⟨#Hinv, Htr, #Hlb⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Ht0; imod Ht1; imod Ht2
  ihave Htr3 : traces3 (GF := GF) γ S.T $$ [Ht0 Ht1 Ht2]
  · unfold traces3; iframe Ht0 Ht1 Ht2
  ihave %hT := traces3_agree' (GF := GF) γ S.T k t' $$ Htr3 Htr
  ihave %hp := traces3_lb (GF := GF) γ S.T k t $$ Htr3 Hlb
  obtain ⟨c, hc⟩ := Hf.run
  have hp' : t <+: projR S.l1 k := by rw [Hf.proj k]; exact hp
  have hpure := pureP.stable_run hc k hp'
  rw [Hf.proj k, hT] at hpure
  rw [hT] at hp
  iunfold traces3 at Htr3
  icases Htr3 with ⟨Ht0, Ht1, Ht2⟩
  imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
    Hcur Hrx Hreqs Hres] with -
  · inext
    iexists S
    iframe
    ipureintro; exact Hf
  imodintro
  iframe Htr
  ipureintro; exact ⟨hp, hpure⟩

/-- **Committed copies in range** (H-X-3; the executor's indexing): every committed or executed
copy of replica `k`'s state has its dependencies inside the instance space (`< SLOTS`) and CAS
commands on key 0 (`cmdsOk`); `crtInstance` is at most `SLOTS`. -/
theorem trace_depsOk (γ : ProtoNames) (k : Fin 3) (t : List Ev) (E : CoPset) (hE : ↑gryffN ⊆ E) :
    gryffInv2 (GF := GF) γ ∗ traceHalf γ k t ⊢
      |={E}=> traceHalf γ k t ∗ ⌜(∀ n c, committedCopy (stOf k t) n = some c →
          (∀ j : Nat, j < 3 → sint.Z (c.deps.at j) < model.SLOTS) ∧ model.cmdsOk c.cmds = true) ∧
        ∀ q : w32, sint.Z ((stOf k t).crt q) ≤ model.SLOTS⌝ := by
  iintro ⟨#Hinv, Htr⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Ht0; imod Ht1; imod Ht2
  ihave Htr3 : traces3 (GF := GF) γ S.T $$ [Ht0 Ht1 Ht2]
  · unfold traces3; iframe Ht0 Ht1 Ht2
  ihave %hT := traces3_agree' (GF := GF) γ S.T k t $$ Htr3 Htr
  obtain ⟨c, hc⟩ := Hf.run
  have hst := real_stOf Hf hc k
  rw [hT] at hst
  have hpure := pureP.depsOk_cfg' hc k
  rw [← hst] at hpure
  iunfold traces3 at Htr3
  icases Htr3 with ⟨Ht0, Ht1, Ht2⟩
  imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
    Hcur Hrx Hreqs Hres] with -
  · inext
    iexists S
    iframe
    ipureintro; exact Hf
  imodintro
  iframe Htr
  ipureintro; exact hpure

end

end Perennial.gryff
