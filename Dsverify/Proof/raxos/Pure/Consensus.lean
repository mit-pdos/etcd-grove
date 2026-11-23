/-
QuePaxa's consensus as a pure transition system over the history of its events (interface of
stage 2, `notes/stage2-plan.md`; stage 1's model, for 3 replicas in leader mode 1, is at the
project's tag `mode1-final`).

The code's state is spread over the replicas' recorders (`recorder.go`, `espImpl`) and the
proposers' loops (`proposer.go`, `handleProposeRequest`); the proof records every step of
theirs that matters to agreement as an event of one global, append-only history `World`
(a ghost mono-list, `Quepaxa/Proof/Ghost.lean`), and `Reach n e W` says that `W` is a history the
code can produce with `n` replicas and epochs of `e` slots: each constructor of `Step` is one kind
of step, with the justification the code has when it takes it (a majority of replies, the
proposer's rules for its next `(S, P)`, the fast path, the slow path, adoption, Go's wrap-around
of `S`, the leader rule of leader mode 2).

* `init i me ids lead`: proxy `me` proposes slot `i` with the batch ids `ids` (`proposeToIndex`,
  `proposePreviousEpochSummary`), at most once per `(i, me)`, as the slot's leader if `lead`
  (`isLeader`: its rank in the slot's leader order is 0);
* `pstate i me lead s P`: a proposer of replica `me` (handling a request with leader flag `lead`)
  is at step `s` with value `P` for slot `i` (each iteration of `handleProposeRequest`'s loop);
* `send i me s v`: it sent `ESP(i, s, v)` to some recorder (`v` is `P`, or `P` with a new random
  priority at a propose step, `variants`);
* `record r i s v st`: recorder `r` processed `ESP(i, s, v)`, its slot state becoming `st`
  (`espStep`), which it returns (`st.S`, `st.F`, `st.M`);
* `decide i ids`: a proposer decided `ids` for slot `i`.

**The leader rule** (leader mode 2, `proxymabhandler.go`): slot `i`'s leader (the first of
`getLeaderSequence(i)`) is, for the first `2n` epochs (`i / e ≤ 2n`), the replicas rotated by the
epoch (`rrLeader`); after them, the first replica of the epoch summary decided in the previous
epoch's first slot (`getLeaderSequenceFromLastEpoch`). An epoch's first slot from epoch `2n` on
(`sumSlot`) proposes a summary (`summaryId p`, `p` a permutation of `1..n`) and nothing else. A
proxy that does not know the previous summary is not the leader (Q6's fix). The fast path is safe
because one proposer per slot proposes with priority `hi` (`leaderOk`, below).

**The agreement theorem** (`agreement`): in a reachable history, every decision of a slot is the
same, is nonempty, and is some proxy's proposal for the slot. Its proof is the protocol's
(QuePaxa, SOSP '23, section 4 and appendix): the propose phase's maximum over a majority's first
proposals, the spread/gather phases' maximum, the fast path's unique high priority.

**Over-approximations** (harmless: they only add behaviors): the fast path is allowed at any step
`≡ 0 mod 4` (the code takes it only at the propose step it is at, `S % 4 == 0` with all replies at
`S`); the slow path compares tags (`isEqualProposal`); `S` wraps at `2^63` as Go's `int` does.

Integers: the Go code's `int`/`int64` values (`sint.Z` of the words), so steps, priorities and
ids are `Int`s in `[-2^63, 2^63)`; `s + 1` wraps (`wrapInc`); `s % 4` is Go's truncated
remainder (`Int.tmod`).
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace Perennial.raxos.pure

/-- The high priority `hi` (`createProposers`: `hi := 100000`). -/
def hi : Int := 100000

/-- The random priorities: `rand.Intn(hi - 10) + 1` (arbitrary in the lab's model). -/
def randPrio (p : Int) : Prop := 1 ≤ p ∧ p ≤ hi - 10

/-- A value: a proposal's priority, proposer id, thread id and client batch ids (the recorder's
`Value`, a proposal's `ProposerMessage_Proposal` without its client batches, a reply's
`RecorderResponse_Proposal`). -/
structure Val where
  prio : Int
  pid : Int
  tid : Int
  ids : List GoString
deriving DecidableEq, Inhabited

/-- The empty value (`-1, -1, -1, nil`), a recorder's initial `F`, `A`, `M`. -/
def Val.bot : Val := ⟨-1, -1, -1, []⟩

/-- `a`'s tag is below `b`'s, lexicographically on (priority, proposer id, thread id) (the
recorder's `max`, the proposer's `isGreaterThan`). -/
def Val.tagLt (a b : Val) : Prop :=
  a.prio < b.prio ∨ (a.prio = b.prio ∧ (a.pid < b.pid ∨ (a.pid = b.pid ∧ a.tid < b.tid)))

instance (a b : Val) : Decidable (a.tagLt b) := by unfold Val.tagLt; infer_instance

/-- Equal tags (the proposer's `isEqualProposal`, on the fields a value has). -/
def Val.tagEq (a b : Val) : Prop := a.prio = b.prio ∧ a.pid = b.pid ∧ a.tid = b.tid

instance (a b : Val) : Decidable (a.tagEq b) := by unfold Val.tagEq; infer_instance

/-- The recorder's `max(old, p)`: `p` if its tag is not below `old`'s (equal tags: `p`). -/
def recMax (old p : Val) : Val := if p.tagLt old then old else p

/-- A recorder's slot (`RecorderSlot`): the step `S`, the first value `F` of the step, the maximum
`A` of the step, the maximum `M` of the previous step. -/
structure RecSt where
  S : Int
  F : Val
  A : Val
  M : Val
deriving DecidableEq, Inhabited

/-- A slot the recorder has not seen (`espImpl`'s new slots). -/
def RecSt.init : RecSt := ⟨0, Val.bot, Val.bot, Val.bot⟩

/-- `espImpl(index, s, p)` on the slot's state. -/
def espStep (st : RecSt) (s : Int) (p : Val) : RecSt :=
  if st.S = s then { st with A := recMax st.A p }
  else if st.S < s then
    let A := if st.S + 1 < s then Val.bot else st.A
    ⟨s, p, p, A⟩
  else st

/-- Go's `S + 1` on an `int` (two's complement, 64 bits). -/
def wrapInc (s : Int) : Int := if s = 2 ^ 63 - 1 then -2 ^ 63 else s + 1

/-! ## The leader rule (leader mode 2) -/

/-- The decimal digits of `k` (`strconv.FormatInt(k, 10)`, `strconv.Itoa`). -/
def decimal (k : Nat) : GoString := (toString k).toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

/-- An epoch summary's id (`proposePreviousEpochSummary`: `"Epoch"` and the replicas of the order
`p`, comma-separated, `calculateSequence`'s string). -/
def summaryId (p : List Nat) : GoString :=
  go!"Epoch" ++ (List.intersperse go!"," (p.map decimal)).flatten

/-- `p` orders the replicas `1..n` (a permutation). -/
def isPerm (n : Nat) (p : List Nat) : Prop := p.Perm (List.range' 1 n)

/-- A summary's order of a deployment's replicas: a permutation of `1..3` or `1..5` (its id
`summaryId p` is at least 10 bytes: the store's command slicing needs 9). -/
def sumPerm (p : List Nat) : Prop := isPerm 3 p ∨ isPerm 5 p

/-- The round-robin leader of slot `i` (`getLeaderSequence(i)[0]` for the first `2n` epochs:
the replicas rotated by `epoch % n`). -/
def rrLeader (n e i : Int) : Int := (i.tdiv e).tmod n + 1

/-- Slot `i` is an epoch's first slot from epoch `2n` on (`isBeginningOfEpoch`): its proposals
are epoch summaries. -/
def sumSlot (n e i : Int) : Prop := 2 * n ≤ i.tdiv e ∧ i = i.tdiv e * e

instance (n e i : Int) : Decidable (sumSlot n e i) := by unfold sumSlot; infer_instance

/-- Replica `me` is slot `i`'s leader by the history `W`: the round-robin leader of the first
`2n` epochs, or the first replica of the summary decided in the previous epoch's first slot. -/
def leaderOk {Ev : Type} (decideEv : Int → List GoString → Ev) (n e : Int) (W : List Ev)
    (i me : Int) : Prop :=
  (i.tdiv e ≤ 2 * n ∧ me = rrLeader n e i) ∨
  (2 * n < i.tdiv e ∧ ∃ p : List Nat, decideEv ((i.tdiv e - 1) * e) [summaryId p] ∈ W ∧
    isPerm n.toNat p ∧ p.head?.map (fun k : Nat => (k : Int)) = some me)

/-- What a proposer with leader flag `lead` at step `s` with value `P` sends to a recorder: `P`,
with a new random priority at a propose step (`S % 4 = 0`) after step 4 or if it is not the
slot's leader (`handleProposeRequest`'s `Pi`). -/
def variants (lead : Bool) (s : Int) (P v : Val) : Prop :=
  if s.tmod 4 = 0 ∧ (s > 4 ∨ lead = false) then
    randPrio v.prio ∧ v.pid = P.pid ∧ v.tid = P.tid ∧ v.ids = P.ids
  else v = P

/-- An event of the history (see the file header). -/
inductive Ev where
  | init (i me : Int) (ids : List GoString) (lead : Bool)
  | pstate (i me : Int) (lead : Bool) (s : Int) (P : Val)
  | send (i me s : Int) (v : Val)
  | record (r i s : Int) (v : Val) (st : RecSt)
  | decide (i : Int) (ids : List GoString)
deriving DecidableEq

/-- The history. -/
abbrev World := List Ev

/-- Recorder `r`'s state of slot `i` after the history `W` (its last `record` event's, or new). -/
def recState (W : World) (r i : Int) : RecSt :=
  W.foldl (fun st e => match e with
    | .record r' i' _ _ st' => if r' = r ∧ i' = i then st' else st
    | _ => st) RecSt.init

/-- The maximum of `f` of the replies, the first maximum in order (`getMaxFromResponses`: the
first reply's, replaced by any strictly greater). -/
def maxOf (f : RecSt → Val) : List RecSt → Val
  | [] => Val.bot
  | st :: sts => sts.foldl (fun m st' => if m.tagLt (f st') then f st' else m) (f st)

/-- The replies a proposer (leader flag `lead`) at step `s` with value `P` collected for slot `i`
with `n` replicas: a majority (`n / 2 + 1`, the number `handleProposeRequest` collects) of
`record` events of `W` for slot `i` at step `s`, at distinct recorders of `1..n`, each for a value
the proposer sends (`variants`), each with a positive step (the proposer drops a reply with
`S = 0`); `sts` their states, in the order collected. -/
def Replies (n : Int) (W : World) (i : Int) (lead : Bool) (s : Int) (P : Val) (sts : List RecSt) :
    Prop :=
  ∃ (rs : List Int) (vs : List Val),
    sts.length = (n / 2 + 1).toNat ∧ rs.length = sts.length ∧ vs.length = sts.length ∧
    rs.Nodup ∧ (∀ r ∈ rs, 1 ≤ r ∧ r ≤ n) ∧
    ∀ (k : Nat) (r : Int) (v : Val) (st : RecSt), rs[k]? = some r → vs[k]? = some v → sts[k]? = some st →
      0 < st.S ∧ Ev.record r i s v st ∈ W ∧ variants lead s P v

/-- One step of the code with `n` replicas and epochs of `e` slots (see the file header). -/
inductive Step (n e : Int) (W : World) : Ev → Prop
  /-- `proposeToIndex`: proxy `me` proposes slot `i` once, with nonempty ids; as the leader only
  if it is the slot's leader by `W`; a summary slot's ids are one summary. -/
  | init (i me : Int) (ids : List GoString) (lead : Bool) :
      (∀ ids' lead', Ev.init i me ids' lead' ∉ W) → ids ≠ [] →
      (lead = true → leaderOk Ev.decide n e W i me) →
      (sumSlot n e i → ∃ p, isPerm n.toNat p ∧ ids = [summaryId p]) →
      Step n e W (.init i me ids lead)
  /-- `handleProposeRequest`'s start: step 4, priority `hi`, the proxy's ids, any thread. -/
  | start (i me tid : Int) (ids : List GoString) (lead : Bool) :
      Ev.init i me ids lead ∈ W → Step n e W (.pstate i me lead 4 ⟨hi, me, tid, ids⟩)
  /-- A call `ESP(i, s, v)` of a proposer at `(s, P)`. -/
  | send (i me : Int) (lead : Bool) (s : Int) (P v : Val) :
      Ev.pstate i me lead s P ∈ W → variants lead s P v → Step n e W (.send i me s v)
  /-- `espImpl` on a sent `(i, s, v)` at recorder `r`. -/
  | record (r i me s : Int) (v : Val) :
      Ev.send i me s v ∈ W → Step n e W (.record r i s v (espStep (recState W r i) s v))
  /-- The fast path: replies at step `s` (`s % 4 = 0`) all with step `s` and a first value of
  priority `hi`: decide the first reply's `F`. -/
  | fast (i me : Int) (lead : Bool) (s : Int) (P : Val) (sts : List RecSt) (st0 : RecSt) :
      Ev.pstate i me lead s P ∈ W → Replies n W i lead s P sts → s.tmod 4 = 0 →
      (∀ st ∈ sts, st.S = s ∧ st.F.prio = hi) → sts.head? = some st0 →
      Step n e W (.decide i st0.F.ids)
  /-- The slow path: replies at step `s` (`s % 4 = 2`) all with step `s`, whose maximum `M` has
  `P`'s tag: decide `P`. -/
  | slow (i me : Int) (lead : Bool) (s : Int) (P : Val) (sts : List RecSt) :
      Ev.pstate i me lead s P ∈ W → Replies n W i lead s P sts → s.tmod 4 = 2 →
      (∀ st ∈ sts, st.S = s) → (maxOf RecSt.M sts).tagEq P →
      Step n e W (.decide i P.ids)
  /-- The next step after replies all at step `s`: the maximum `F` after a propose step, the
  maximum `M` after step `4k+3`, `P` otherwise (`S + 1`, wrapping). -/
  | next (i me : Int) (lead : Bool) (s : Int) (P : Val) (sts : List RecSt) :
      Ev.pstate i me lead s P ∈ W → Replies n W i lead s P sts → (∀ st ∈ sts, st.S = s) →
      Step n e W (.pstate i me lead (wrapInc s)
        (if s.tmod 4 = 0 then maxOf RecSt.F sts
         else if s.tmod 4 = 3 then maxOf RecSt.M sts else P))
  /-- Adoption: a reply of a later step `S'`: `(S', F')`. -/
  | adopt (i me : Int) (lead : Bool) (s : Int) (P : Val) (sts : List RecSt) (st : RecSt) :
      Ev.pstate i me lead s P ∈ W → Replies n W i lead s P sts → st ∈ sts → s < st.S →
      Step n e W (.pstate i me lead st.S st.F)

/-- The histories the code can produce with `n` replicas and epochs of `e` slots. -/
inductive Reach (n e : Int) : World → Prop
  | nil : Reach n e []
  | step (W : World) (ev : Ev) : Reach n e W → Step n e W ev → Reach n e (W ++ [ev])

/-! ## The proof of agreement (package `pure`)

An inductive invariant `AgreeInv.Inv` over `Reach` (`AgreeInv.inv_of_reach`), whose clauses are
each stable under appending events, then the agreement argument on the final history by induction
on the step number (`AgreeInv.Inv.good_from`): a fast decision (only at step 4) fixes the ids of
the slot's leader's `init` from step 5 on (all `lead` inits of a slot are by one replica, clause
`lu`, kept at a new `init` by agreement on the history so far, `AgreeInv.leaderOk_unique`, and the
first replica of a summary is determined by its id, `AgreeInv.summaryId_head`); a slow decision of
`P` at step `4k+2` bounds every value at that step by `P` and fixes `P`'s ids from step `4k+4` on.
Majorities of `[1, n]` intersect (`AgreeInv.quorum`). See `notes/pkg-pure.md`.
-/

namespace AgreeInv

/-! ### Tags -/

/-- `a`'s tag is at most `b`'s. -/
def le (a b : Val) : Prop := ¬ b.tagLt a

theorem le_refl (a : Val) : le a a := by unfold le Val.tagLt; omega
theorem le_trans {a b c : Val} (h1 : le a b) (h2 : le b c) : le a c := by
  unfold le Val.tagLt at *; omega
theorem le_prio {a b : Val} (h : le a b) : a.prio ≤ b.prio := by unfold le Val.tagLt at *; omega
theorem le_of_tagEq {a b : Val} (h : a.tagEq b) : le a b := by
  unfold le Val.tagLt Val.tagEq at *; omega
theorem tagEq_of_le {a b : Val} (h1 : le a b) (h2 : le b a) : a.tagEq b := by
  unfold le Val.tagLt Val.tagEq at *; omega
theorem le_recMax_left (o p : Val) : le o (recMax o p) := by
  unfold recMax; split
  · exact le_refl _
  · unfold le Val.tagLt at *; omega
theorem le_recMax_right (o p : Val) : le p (recMax o p) := by
  unfold recMax; split
  · unfold le Val.tagLt at *; omega
  · exact le_refl _
theorem recMax_cases (o p : Val) : recMax o p = o ∨ recMax o p = p := by
  unfold recMax; split <;> simp
theorem bot_le {a : Val} (h : 1 ≤ a.prio) : le Val.bot a := by
  unfold le Val.tagLt Val.bot; simp; omega

/-! ### The maximum of replies -/

theorem foldl_max (f : RecSt → Val) (sts : List RecSt) (m : Val) :
    (sts.foldl (fun m st' => if m.tagLt (f st') then f st' else m) m = m ∨
      ∃ st ∈ sts, sts.foldl (fun m st' => if m.tagLt (f st') then f st' else m) m = f st) ∧
    le m (sts.foldl (fun m st' => if m.tagLt (f st') then f st' else m) m) ∧
    ∀ st ∈ sts, le (f st) (sts.foldl (fun m st' => if m.tagLt (f st') then f st' else m) m) := by
  induction sts generalizing m with
  | nil => exact ⟨.inl rfl, le_refl _, by simp⟩
  | cons a sts ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (if m.tagLt (f a) then f a else m)
    have g1 : le m (if m.tagLt (f a) then f a else m) := by
      split
      · unfold le Val.tagLt at *; omega
      · exact le_refl _
    have g2 : le (f a) (if m.tagLt (f a) then f a else m) := by
      split
      · exact le_refl _
      · unfold le; assumption
    refine ⟨?_, le_trans g1 h2, ?_⟩
    · rcases h1 with h | ⟨st, hst, h⟩
      · rw [h]; split
        · exact .inr ⟨a, by simp, rfl⟩
        · exact .inl rfl
      · exact .inr ⟨st, by simp [hst], h⟩
    · intro st hst
      simp only [List.mem_cons] at hst
      rcases hst with rfl | hst
      · exact le_trans g2 h2
      · exact h3 st hst

theorem maxOf_mem (f : RecSt → Val) {sts : List RecSt} (h : sts ≠ []) :
    ∃ st ∈ sts, maxOf f sts = f st := by
  cases sts with
  | nil => exact absurd rfl h
  | cons a sts =>
    rcases (foldl_max f sts (f a)).1 with h' | ⟨st, hst, h'⟩
    · exact ⟨a, by simp, h'⟩
    · exact ⟨st, by simp [hst], h'⟩

theorem maxOf_ge (f : RecSt → Val) {sts : List RecSt} {st : RecSt} (h : st ∈ sts) :
    le (f st) (maxOf f sts) := by
  cases sts with
  | nil => simp at h
  | cons a sts =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact (foldl_max f sts (f st)).2.1
    · exact (foldl_max f sts (f a)).2.2 st h

/-! ### Majorities -/

/-- Two majorities of `[1, n]` intersect. -/
theorem quorum {n : Int} (hn : 1 ≤ n) {rs qs : List Int} (hr : rs.Nodup) (hq : qs.Nodup)
    (hr1 : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ n) (hq1 : ∀ r ∈ qs, 1 ≤ r ∧ r ≤ n)
    (hrl : rs.length = (n / 2 + 1).toNat) (hql : qs.length = (n / 2 + 1).toNat) :
    ∃ r, r ∈ rs ∧ r ∈ qs := by
  apply Classical.byContradiction
  intro hno
  have hd : (rs ++ qs).Nodup := List.nodup_append.2 ⟨hr, hq, fun a ha b hb hab => by
    subst hab; exact hno ⟨a, ha, hb⟩⟩
  have hsub : rs ++ qs ⊆ (List.range' 1 n.toNat).map (fun k : Nat => (k : Int)) := by
    intro x hx
    have hx' : 1 ≤ x ∧ x ≤ n := by
      rcases List.mem_append.1 hx with h | h
      · exact hr1 x h
      · exact hq1 x h
    simp only [List.mem_map, List.mem_range'_1]
    exact ⟨x.toNat, by omega, by omega⟩
  have := hd.length_le_of_subset hsub
  simp only [List.length_append, List.length_map, List.length_range'] at this
  omega

theorem Replies.mem {n W i l s P sts st} (h : Replies n W i l s P sts) (hst : st ∈ sts) :
    ∃ r v, Ev.record r i s v st ∈ W ∧ 0 < st.S ∧ variants l s P v := by
  obtain ⟨rs, vs, hl, hrl, hvl, -, -, hk⟩ := h
  obtain ⟨k, hk1⟩ := List.mem_iff_getElem?.1 hst
  have hks : k < sts.length := by
    rcases Nat.lt_or_ge k sts.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk1; cases hk1
  have h1 : rs[k]? = some rs[k] := List.getElem?_eq_getElem (by omega)
  have h2 : vs[k]? = some vs[k] := List.getElem?_eq_getElem (by omega)
  obtain ⟨a, b, c⟩ := hk k _ _ _ h1 h2 hk1
  exact ⟨_, _, b, a, c⟩

theorem Replies.ne {n W i l s P sts} (hn : 1 ≤ n) (h : Replies n W i l s P sts) : sts ≠ [] := by
  obtain ⟨rs, vs, hl, -⟩ := h
  intro h; subst h; simp at hl; omega

/-- Two majorities of replies of a slot share a recorder. -/
theorem Replies.inter {n W i l s P sts l' s' P' sts'} (hn : 1 ≤ n) (h : Replies n W i l s P sts)
    (h' : Replies n W i l' s' P' sts') :
    ∃ r v st v' st', st ∈ sts ∧ st' ∈ sts' ∧ Ev.record r i s v st ∈ W ∧
      Ev.record r i s' v' st' ∈ W ∧ 0 < st.S ∧ 0 < st'.S ∧ variants l s P v ∧
      variants l' s' P' v' := by
  obtain ⟨rs, vs, hl, hrl, hvl, hnd, hr1, hk⟩ := h
  obtain ⟨qs, ws, hl', hql, hwl, hnd', hq1, hk'⟩ := h'
  obtain ⟨r, hr, hq⟩ := quorum hn hnd hnd' hr1 hq1 (by omega) (by omega)
  obtain ⟨k, hk1⟩ := List.mem_iff_getElem?.1 hr
  obtain ⟨k', hk1'⟩ := List.mem_iff_getElem?.1 hq
  have hks : k < rs.length := by
    rcases Nat.lt_or_ge k rs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk1; cases hk1
  have hks' : k' < qs.length := by
    rcases Nat.lt_or_ge k' qs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk1'; cases hk1'
  have h2 : vs[k]? = some vs[k] := List.getElem?_eq_getElem (by omega)
  have h3 : sts[k]? = some sts[k] := List.getElem?_eq_getElem (by omega)
  have h2' : ws[k']? = some ws[k'] := List.getElem?_eq_getElem (by omega)
  have h3' : sts'[k']? = some sts'[k'] := List.getElem?_eq_getElem (by omega)
  obtain ⟨a, b, c⟩ := hk k _ _ _ hk1 h2 h3
  obtain ⟨a', b', c'⟩ := hk' k' _ _ _ hk1' h2' h3'
  exact ⟨r, _, _, _, _, List.getElem_mem _, List.getElem_mem _, b, b', a, a', c, c'⟩

theorem Replies.mono {n W W'} (hW : ∀ e ∈ W, e ∈ W') {i l s P sts}
    (h : Replies n W i l s P sts) : Replies n W' i l s P sts := by
  obtain ⟨rs, vs, a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨rs, vs, a1, a2, a3, a4, a5, fun k r v st h1 h2 h3 =>
    let ⟨b1, b2, b3⟩ := a6 k r v st h1 h2 h3; ⟨b1, hW _ b2, b3⟩⟩

end AgreeInv
namespace AgreeInv

theorem ba_loop (bs : ByteArray) (i : Nat) (r : List UInt8) (hi : i ≤ bs.size) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  have hsz : bs.data.toList.length = bs.size := Array.length_toList
  induction h : bs.size - i generalizing i r with
  | zero =>
    have : i = bs.size := by omega
    subst this
    rw [ByteArray.toList.loop, ite_eq_right_of_eq_false _ _ (by simp)]
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ k ih =>
    have hlt : i < bs.size := by omega
    rw [ByteArray.toList.loop, ite_eq_left_of_eq_true _ _ (by simp [hlt]), ih (i + 1) _ (by omega) (by omega)]
    have hl : i < bs.data.toList.length := by omega
    have : bs.get! i = bs.data.toList[i] := by
      rw [ByteArray.get!, getElem!_pos bs.data i (by omega), Array.getElem_toList]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, this, List.getElem_cons_drop]

theorem ba_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, ba_loop _ _ _ (Nat.zero_le _)]; simp

/-- `decimal k` is the digits' bytes. -/
theorem decimal_eq (k : Nat) :
    decimal k = (Nat.toDigits 10 k).map (fun c => BitVec.ofNat 8 c.val.toNat) := by
  unfold decimal
  rw [Nat.toString_eq_ofList_toDigits, ba_toList, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray]
  have : ∀ cs : List Char, (∀ c ∈ cs, c.isDigit) →
      (cs.flatMap String.utf8EncodeChar).map (fun b => BitVec.ofNat 8 b.toNat) =
      cs.map (fun c => BitVec.ofNat 8 c.val.toNat) := by
    intro cs hcs
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      have hd := hcs c (by simp)
      simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
      have hhi : c.val.toNat ≤ 57 := hd.2
      have h1 : c.utf8Size = 1 := Char.utf8Size_eq_one_iff.2 (by
        rw [UInt32.le_iff_toNat_le]; have : c.toNat = c.val.toNat := rfl; simp; omega)
      rw [List.flatMap_cons, String.utf8EncodeChar_eq_singleton h1, List.map_append,
        ih (fun c' h' => hcs c' (by simp [h']))]
      have : c.val.toUInt8.toNat = c.val.toNat := by rw [UInt32.toNat_toUInt8]; omega
      simp only [List.map_cons, List.map_nil, List.singleton_append, List.cons.injEq, and_true]
      rw [this]
  exact this _ (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

theorem decimal_digit (k : Nat) : ∀ b ∈ decimal k, 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  rw [decimal_eq]; intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  have hd := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  have hlo : 48 ≤ c.val.toNat := hd.1
  have hhi : c.val.toNat ≤ 57 := hd.2
  simp only [BitVec.toNat_ofNat]; omega

theorem decimal_ne (k : Nat) : decimal k ≠ [] := by
  rw [decimal_eq]; simp [Nat.toDigits_ne_nil]

theorem decimal_inj {a b : Nat} (h : decimal a = decimal b) : a = b := by
  rw [decimal_eq, decimal_eq] at h
  have hm : ∀ (l1 l2 : List Char), (∀ c ∈ l1, c.isDigit) → (∀ c ∈ l2, c.isDigit) →
      l1.map (fun c => BitVec.ofNat 8 c.val.toNat) = l2.map (fun c => BitVec.ofNat 8 c.val.toNat) →
      l1 = l2 := by
    intro l1
    induction l1 with
    | nil => intro l2 _ _ h; cases l2 <;> simp_all
    | cons c l1 ih =>
      intro l2 h1 h2 h
      cases l2 with
      | nil => simp at h
      | cons c' l2 =>
        simp only [List.map_cons, List.cons.injEq] at h
        have d1 := h1 c (by simp); have d2 := h2 c' (by simp)
        simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at d1 d2
        have e1 : c.val.toNat ≤ 57 := d1.2
        have e2 : c'.val.toNat ≤ 57 := d2.2
        have := congrArg BitVec.toNat h.1
        simp only [BitVec.toNat_ofNat] at this
        have hcc : c = c' := by
          apply Char.ext; apply UInt32.toNat_inj.1; omega
        rw [hcc, ih l2 (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx])) h.2]
  have := hm _ _ (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
    (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc) h
  rw [← Nat.ofDigitChars_ten_toDigits (n := a), ← Nat.ofDigitChars_ten_toDigits (n := b), this]

theorem split_comma (A A' B B' : List w8) (hA : ∀ b ∈ A, b ≠ 44#8) (hA' : ∀ b ∈ A', b ≠ 44#8)
    (hB : B = [] ∨ B.head? = some 44#8) (hB' : B' = [] ∨ B'.head? = some 44#8)
    (h : A ++ B = A' ++ B') : A = A' := by
  induction A generalizing A' with
  | nil =>
    cases A' with
    | nil => rfl
    | cons a A' =>
      simp only [List.nil_append, List.cons_append] at h
      subst h
      rcases hB with h | h
      · simp at h
      · simp at h; exact absurd h (hA' a (by simp))
  | cons a A ih =>
    cases A' with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h
      subst h
      rcases hB' with h | h
      · simp at h
      · simp at h; exact absurd h (hA a (by simp))
    | cons a' A' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      rw [ih A' (fun b hb => hA b (by simp [hb])) (fun b hb => hA' b (by simp [hb])) h]

theorem summaryId_split (a : Nat) (l : List Nat) :
    ∃ B : List w8, (B = [] ∨ B.head? = some 44#8) ∧
      (List.intersperse go!"," ((a :: l).map decimal)).flatten = decimal a ++ B := by
  cases l with
  | nil => exact ⟨[], .inl rfl, by simp⟩
  | cons b l =>
    refine ⟨go!"," ++ (List.intersperse go!"," ((b :: l).map decimal)).flatten, .inr ?_, ?_⟩
    · rfl
    · simp [List.intersperse_cons_cons]

theorem decimal_ne_comma (k : Nat) : ∀ b ∈ decimal k, b ≠ 44#8 := by
  intro b hb h; have := decimal_digit k b hb; subst h; simp at this

theorem summaryId_head {p p' : List Nat} (h : summaryId p = summaryId p') : p.head? = p'.head? := by
  unfold summaryId at h
  have h := List.append_cancel_left h
  cases p with
  | nil =>
    cases p' with
    | nil => rfl
    | cons a' l' =>
      obtain ⟨B', -, e'⟩ := summaryId_split a' l'
      rw [e'] at h; simp at h; exact absurd h.1 (decimal_ne a')
  | cons a l =>
    cases p' with
    | nil =>
      obtain ⟨B, -, e⟩ := summaryId_split a l
      rw [e] at h; simp at h; exact absurd h.1 (decimal_ne a)
    | cons a' l' =>
      obtain ⟨B, hB, e⟩ := summaryId_split a l
      obtain ⟨B', hB', e'⟩ := summaryId_split a' l'
      rw [e, e'] at h
      have := split_comma _ _ _ _ (decimal_ne_comma a) (decimal_ne_comma a') hB hB' h
      simp [decimal_inj this]

end AgreeInv
namespace AgreeInv

/-! ### Integers and histories -/

theorem tmod_pos {t : Int} (h : 0 ≤ t) : t.tmod 4 = t % 4 := Int.tmod_eq_emod_of_nonneg h

theorem wrapInc_pos {s t : Int} (h : wrapInc s = t) (ht : 0 < t) : s = t - 1 := by
  unfold wrapInc at h; split at h <;> omega

theorem recState_snoc (W : World) (e : Ev) (r i : Int) :
    recState (W ++ [e]) r i = match e with
      | .record r' i' _ _ st' => if r' = r ∧ i' = i then st' else recState W r i
      | _ => recState W r i := by
  unfold recState; rw [List.foldl_append]; cases e <;> simp

theorem Step.decide_mono {n e W W'} (hW : ∀ x ∈ W, x ∈ W') {i a}
    (h : Step n e W (.decide i a)) : Step n e W' (.decide i a) := by
  cases h with
  | fast _ me l s P sts st0 h1 h2 h3 h4 h5 =>
    exact .fast i me l s P sts st0 (hW _ h1) (Replies.mono hW h2) h3 h4 h5
  | slow _ me l s P sts h1 h2 h3 h4 h5 =>
    exact .slow i me l s P sts (hW _ h1) (Replies.mono hW h2) h3 h4 h5

theorem leaderOk.mono {n e W W'} (hW : ∀ x ∈ W, x ∈ W') {i me}
    (h : leaderOk Ev.decide n e W i me) : leaderOk Ev.decide n e W' i me := by
  rcases h with h | ⟨h1, p, h2, h3, h4⟩
  · exact .inl h
  · exact .inr ⟨h1, p, hW _ h2, h3, h4⟩

/-! ### The invariant -/

/-- A real value: a priority in `[1, hi]` and the ids of its proposer's `init`. -/
def Real (W : World) (i : Int) (v : Val) : Prop :=
  1 ≤ v.prio ∧ v.prio ≤ hi ∧ ∃ l, Ev.init i v.pid v.ids l ∈ W

def sentAt (W : World) (i s : Int) (v : Val) : Prop := ∃ me, Ev.send i me s v ∈ W

/-- A recorder state's values are sent ones. -/
def SF (W : World) (i : Int) (st : RecSt) : Prop :=
  st = RecSt.init ∨ (0 < st.S ∧ sentAt W i st.S st.F ∧ sentAt W i st.S st.A ∧
    (st.M = Val.bot ∨ sentAt W i (st.S - 1) st.M))

/-- An earlier state `st` of a recorder whose current state is `c`. -/
def Below (st c : RecSt) : Prop :=
  st.S ≤ c.S ∧ (st.S = c.S → st.F = c.F ∧ st.M = c.M ∧ le st.A c.A) ∧
    (0 < st.S → st.S + 1 = c.S → le st.A c.M)

def RecOK (W : World) (r i s : Int) (v : Val) (st : RecSt) : Prop :=
  sentAt W i s v ∧ SF W i st ∧ s ≤ st.S ∧ (st.S = s → le v st.A) ∧ Below st (recState W r i)

/-- The proposer's next value after replies at step `s`. -/
def nextVal (s : Int) (P : Val) (sts : List RecSt) : Val :=
  if s.tmod 4 = 0 then maxOf RecSt.F sts else if s.tmod 4 = 3 then maxOf RecSt.M sts else P

/-- Same proposal, up to the priority at a propose step. -/
def sim (t : Int) (a b : Val) : Prop :=
  a.pid = b.pid ∧ a.tid = b.tid ∧ a.ids = b.ids ∧ (t.tmod 4 ≠ 0 → a = b)

theorem sim_refl (t : Int) (a : Val) : sim t a a := ⟨rfl, rfl, rfl, fun _ => rfl⟩
theorem sim_trans {t : Int} {a b c : Val} (h1 : sim t a b) (h2 : sim t b c) : sim t a c := by
  obtain ⟨a1, a2, a3, a4⟩ := h1; obtain ⟨b1, b2, b3, b4⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, fun h => (a4 h).trans (b4 h)⟩

theorem variants_sim {l t P v} (h : variants l t P v) : sim t v P := by
  unfold variants at h; by_cases hc : t.tmod 4 = 0 ∧ (t > 4 ∨ l = false)
  · simp only [hc] at h; obtain ⟨_, h1, h2, h3⟩ := h; exact ⟨h1, h2, h3, fun h' => absurd hc.1 h'⟩
  · simp only [hc] at h; subst h; exact sim_refl _ _

/-- A value sent at step 4 with priority `hi` is the proposer's value, of a leader. -/
theorem variants_hi4 {l P v} (h : variants l 4 P v) (hhi : v.prio = hi) : l = true ∧ v = P := by
  unfold variants at h
  by_cases hc : (4 : Int).tmod 4 = 0 ∧ ((4 : Int) > 4 ∨ l = false)
  · simp only [hc] at h; have := h.1.2; unfold hi at *; omega
  · simp only [hc] at h
    refine ⟨?_, h⟩
    cases l
    · exact absurd ⟨by decide, .inr rfl⟩ hc
    · rfl

/-- A pstate at `t` is (up to `sim`) the `next` of replies at step `t - 1`. -/
def NormAt (n : Int) (W : World) (i t : Int) (P : Val) : Prop :=
  ∃ me' l Q sts, Ev.pstate i me' l (t - 1) Q ∈ W ∧ Replies n W i l (t - 1) Q sts ∧
    (∀ st ∈ sts, st.S = t - 1) ∧ sim t P (nextVal (t - 1) Q sts)

structure Inv (n e : Int) (W : World) : Prop where
  uniq : ∀ i me a b la lb, Ev.init i me a la ∈ W → Ev.init i me b lb ∈ W → a = b ∧ la = lb
  ne : ∀ i me a l, Ev.init i me a l ∈ W → a ≠ []
  lok : ∀ i me a, Ev.init i me a true ∈ W → leaderOk Ev.decide n e W i me
  lu : ∀ i me me' a b, Ev.init i me a true ∈ W → Ev.init i me' b true ∈ W → me = me'
  send : ∀ i me s v, Ev.send i me s v ∈ W → ∃ l P, Ev.pstate i me l s P ∈ W ∧ variants l s P v
  dec : ∀ i a, Ev.decide i a ∈ W → Step n e W (.decide i a)
  low : ∀ i me l t P, Ev.pstate i me l t P ∈ W → t < 0 ∨ 4 ≤ t
  real : ∀ i me l t P, Ev.pstate i me l t P ∈ W → Real W i P
  lead : ∀ i me P, Ev.pstate i me true 4 P ∈ W → P.prio = hi → Ev.init i P.pid P.ids true ∈ W
  norm : ∀ i me l t P, Ev.pstate i me l t P ∈ W → 0 < t → t ≠ 4 → NormAt n W i t P
  cur : ∀ r i, 0 ≤ (recState W r i).S ∧ SF W i (recState W r i)
  recs : ∀ r i s v st, Ev.record r i s v st ∈ W → RecOK W r i s v st
  pair : ∀ r i s1 v1 st1 s2 v2 st2, Ev.record r i s1 v1 st1 ∈ W → Ev.record r i s2 v2 st2 ∈ W →
    0 < st1.S → (st1.S = st2.S → st1.F = st2.F ∧ st1.M = st2.M) ∧
      (st1.S + 1 = st2.S → le st1.A st2.M)

theorem mem_snoc {x e : Ev} {W : World} : x ∈ W ++ [e] ↔ x ∈ W ∨ x = e := by simp

theorem sub_snoc (W : World) (e : Ev) : ∀ x ∈ W, x ∈ W ++ [e] := fun _ h => mem_snoc.2 (.inl h)

section mono
variable {W W' : World} (hW : ∀ e ∈ W, e ∈ W')
include hW
theorem Real.mono {i v} (h : Real W i v) : Real W' i v :=
  ⟨h.1, h.2.1, let ⟨l, h⟩ := h.2.2; ⟨l, hW _ h⟩⟩
theorem sentAt.mono {i s v} (h : sentAt W i s v) : sentAt W' i s v :=
  let ⟨me, h⟩ := h; ⟨me, hW _ h⟩
theorem SF.mono {i st} (h : SF W i st) : SF W' i st := by
  rcases h with h | ⟨h1, h2, h3, h4⟩
  · exact .inl h
  · exact .inr ⟨h1, h2.mono hW, h3.mono hW, h4.imp id (sentAt.mono hW)⟩
theorem NormAt.mono {n i t P} (h : NormAt n W i t P) : NormAt n W' i t P := by
  obtain ⟨me', l, Q, sts, h1, h2, h3, h4⟩ := h
  exact ⟨me', l, Q, sts, hW _ h1, Replies.mono hW h2, h3, h4⟩
end mono

theorem real_variant {W i l s P v} (h : Real W i P) (hv : variants l s P v) : Real W i v := by
  unfold variants at hv
  by_cases hc : s.tmod 4 = 0 ∧ (s > 4 ∨ l = false)
  · simp only [hc] at hv
    obtain ⟨⟨h1, h2⟩, h3, _, h5⟩ := hv
    refine ⟨h1, by unfold hi at *; omega, ?_⟩
    rw [h3, h5]; exact h.2.2
  · simp only [hc] at hv; subst hv; exact h

section inv
variable {n e : Int} {W : World} (I : Inv n e W)
include I

theorem Inv.sent_ps {i s v} (h : sentAt W i s v) :
    ∃ me l P, Ev.pstate i me l s P ∈ W ∧ variants l s P v :=
  let ⟨me, h⟩ := h; let ⟨l, P, h1, h2⟩ := I.send _ _ _ _ h; ⟨me, l, P, h1, h2⟩

theorem Inv.sent_real {i s v} (h : sentAt W i s v) : Real W i v :=
  let ⟨_, _, _, h1, h2⟩ := I.sent_ps h; real_variant (I.real _ _ _ _ _ h1) h2

theorem Inv.sent_low {i s v} (h : sentAt W i s v) : s < 0 ∨ 4 ≤ s :=
  let ⟨_, _, _, h1, _⟩ := I.sent_ps h; I.low _ _ _ _ _ h1

theorem Inv.rec_sf {r i s v st} (h : Ev.record r i s v st ∈ W) (hS : 0 < st.S) :
    sentAt W i st.S st.F ∧ sentAt W i st.S st.A ∧ (st.M = Val.bot ∨ sentAt W i (st.S - 1) st.M) := by
  rcases (I.recs _ _ _ _ _ h).2.1 with h' | ⟨_, h2, h3, h4⟩
  · subst h'; simp [RecSt.init] at hS
  · exact ⟨h2, h3, h4⟩

theorem Inv.real_ne {i v} (h : Real W i v) : v.ids ≠ [] :=
  let ⟨_, h⟩ := h.2.2; I.ne _ _ _ _ h

theorem Inv.real_ids {i a b} (ha : Real W i a) (hb : Real W i b) (h : a.pid = b.pid) :
    a.ids = b.ids := by
  obtain ⟨la, ha⟩ := ha.2.2; obtain ⟨lb, hb⟩ := hb.2.2
  rw [← h] at hb; exact (I.uniq _ _ _ _ _ _ ha hb).1

/-- A value sent at step 4 with priority `hi` is a leader's proposal. -/
theorem Inv.sent4hi {i v} (h : sentAt W i 4 v) (hhi : v.prio = hi) :
    Ev.init i v.pid v.ids true ∈ W := by
  obtain ⟨me1, l1, P1, hP1, hv1⟩ := I.sent_ps h
  obtain ⟨rfl, rfl⟩ := variants_hi4 hv1 hhi
  exact I.lead _ _ _ hP1 hhi

end inv

/-- Appending an event other than a `record`, given its own clauses. -/
theorem Inv.extend {n e : Int} {W : World} (I : Inv n e W) (x : Ev)
    (hinit : ∀ i me a l, x = .init i me a l → (∀ b l', Ev.init i me b l' ∉ W) ∧ a ≠ [] ∧
      (l = true → leaderOk Ev.decide n e W i me ∧ ∀ me' b, Ev.init i me' b true ∈ W → me' = me))
    (hsend : ∀ i me s v, x = .send i me s v → ∃ l P, Ev.pstate i me l s P ∈ W ∧ variants l s P v)
    (hdec : ∀ i a, x = .decide i a → Step n e W (.decide i a))
    (hps : ∀ i me l t P, x = .pstate i me l t P → (t < 0 ∨ 4 ≤ t) ∧ Real W i P ∧
      (l = true → t = 4 → P.prio = hi → Ev.init i P.pid P.ids true ∈ W) ∧
      (0 < t → t ≠ 4 → NormAt n W i t P))
    (hrec : ∀ r i s v st, x ≠ .record r i s v st) : Inv n e (W ++ [x]) := by
  have hW := sub_snoc W x
  have hcur : ∀ r i, recState (W ++ [x]) r i = recState W r i := by
    intro r i; rw [recState_snoc]
    cases x with
    | record r' i' s' v' st' => exact absurd rfl (hrec r' i' s' v' st')
    | _ => rfl
  constructor
  · intro i me a b la lb ha hb
    rcases mem_snoc.1 ha with ha | ha <;> rcases mem_snoc.1 hb with hb | hb
    · exact I.uniq _ _ _ _ _ _ ha hb
    · exact absurd ha ((hinit _ _ _ _ hb.symm).1 a la)
    · exact absurd hb ((hinit _ _ _ _ ha.symm).1 b lb)
    · rw [← hb] at ha; cases ha; exact ⟨rfl, rfl⟩
  · intro i me a l ha
    rcases mem_snoc.1 ha with ha | ha
    · exact I.ne _ _ _ _ ha
    · exact (hinit _ _ _ _ ha.symm).2.1
  · intro i me a ha
    rcases mem_snoc.1 ha with ha | ha
    · exact leaderOk.mono hW (I.lok _ _ _ ha)
    · exact leaderOk.mono hW ((hinit _ _ _ _ ha.symm).2.2 rfl).1
  · intro i me me' a b ha0 hb0
    rcases mem_snoc.1 ha0 with ha | ha <;> rcases mem_snoc.1 hb0 with hb | hb
    · exact I.lu _ _ _ _ _ ha hb
    · exact ((hinit _ _ _ _ hb.symm).2.2 rfl).2 _ _ ha
    · exact (((hinit _ _ _ _ ha.symm).2.2 rfl).2 _ _ hb).symm
    · rw [← hb] at ha; cases ha; rfl
  · intro i me s v h
    rcases mem_snoc.1 h with h | h
    · obtain ⟨l, P, h1, h2⟩ := I.send _ _ _ _ h; exact ⟨l, P, hW _ h1, h2⟩
    · obtain ⟨l, P, h1, h2⟩ := hsend _ _ _ _ h.symm; exact ⟨l, P, hW _ h1, h2⟩
  · intro i a h
    rcases mem_snoc.1 h with h | h
    · exact Step.decide_mono hW (I.dec _ _ h)
    · exact Step.decide_mono hW (hdec _ _ h.symm)
  · intro i me l t P h
    rcases mem_snoc.1 h with h | h
    · exact I.low _ _ _ _ _ h
    · exact (hps _ _ _ _ _ h.symm).1
  · intro i me l t P h
    rcases mem_snoc.1 h with h | h
    · exact (I.real _ _ _ _ _ h).mono hW
    · exact (hps _ _ _ _ _ h.symm).2.1.mono hW
  · intro i me P h hhi
    rcases mem_snoc.1 h with h | h
    · exact hW _ (I.lead _ _ _ h hhi)
    · exact hW _ ((hps _ _ _ _ _ h.symm).2.2.1 rfl rfl hhi)
  · intro i me l t P h h1 h2
    rcases mem_snoc.1 h with h | h
    · exact (I.norm _ _ _ _ _ h h1 h2).mono hW
    · exact ((hps _ _ _ _ _ h.symm).2.2.2 h1 h2).mono hW
  · intro r i; rw [hcur]; exact ⟨(I.cur r i).1, (I.cur r i).2.mono hW⟩
  · intro r i s v st h
    rcases mem_snoc.1 h with h | h
    · obtain ⟨h1, h2, h3, h4, h5⟩ := I.recs _ _ _ _ _ h
      exact ⟨h1.mono hW, h2.mono hW, h3, h4, by rw [hcur]; exact h5⟩
    · exact absurd h.symm (hrec _ _ _ _ _)
  · intro r i s1 v1 st1 s2 v2 st2 h1 h2
    rcases mem_snoc.1 h1 with h1 | h1
    · rcases mem_snoc.1 h2 with h2 | h2
      · exact I.pair _ _ _ _ _ _ _ _ h1 h2
      · exact absurd h2.symm (hrec _ _ _ _ _)
    · exact absurd h1.symm (hrec _ _ _ _ _)

end AgreeInv
namespace AgreeInv

/-- Two leaders of a slot by the history are the same replica, given agreement on the history. -/
theorem leaderOk_unique {n e W i me me'}
    (hag : ∀ j a b, Ev.decide j a ∈ W → Ev.decide j b ∈ W → a = b)
    (h : leaderOk Ev.decide n e W i me) (h' : leaderOk Ev.decide n e W i me') : me = me' := by
  rcases h with ⟨h1, rfl⟩ | ⟨h1, p, h2, -, h4⟩ <;>
    rcases h' with ⟨h1', rfl⟩ | ⟨h1', p', h2', -, h4'⟩
  · rfl
  · omega
  · omega
  · have := hag _ _ _ h2 h2'
    simp only [List.cons.injEq, and_true] at this
    have hh := summaryId_head this
    rw [hh] at h4; rw [h4] at h4'; cases h4'; rfl

section inv
variable {n e : Int} {W : World} (I : Inv n e W) (hn : 1 ≤ n)
include I hn

omit hn in
theorem Inv.M_real {r i s v st} (h : Ev.record r i s v st ∈ W) (hS : 0 < st.S)
    (hp : 1 ≤ st.M.prio) : Real W i st.M := by
  rcases (I.rec_sf h hS).2.2 with h' | h'
  · rw [h'] at hp; simp [Val.bot] at hp
  · exact I.sent_real h'

omit hn in
theorem Inv.A_pos {r i s v st} (h : Ev.record r i s v st ∈ W) (hS : st.S = s) :
    1 ≤ st.A.prio := by
  obtain ⟨h1, -, -, h4, -⟩ := I.recs _ _ _ _ _ h
  exact Int.le_trans (I.sent_real h1).1 (le_prio (h4 hS))

/-- The nonempty argument: after replies at a step `4k+3`, some reply's `M` is real. -/
theorem Inv.next_real {i me l s P sts} (hP : Ev.pstate i me l s P ∈ W)
    (hR : Replies n W i l s P sts) (hS : ∀ st ∈ sts, st.S = s) : Real W i (nextVal s P sts) := by
  have hne := Replies.ne hn hR
  unfold nextVal
  split
  · obtain ⟨st, hst, h⟩ := maxOf_mem RecSt.F hne
    obtain ⟨r, v, hm, hp, -⟩ := Replies.mem hR hst
    rw [h]; exact I.sent_real (I.rec_sf hm hp).1
  split
  · rename_i h3
    obtain ⟨st0, hst0⟩ := List.exists_mem_of_ne_nil sts hne
    obtain ⟨r0, v0, -, hp0, -⟩ := Replies.mem hR hst0
    have hs0 : 0 < s := hS _ hst0 ▸ hp0
    have hs4 : s ≠ 4 := by intro h; subst h; simp at h3
    obtain ⟨me', l', Q, sts', -, hR', hS', -⟩ := I.norm _ _ _ _ _ hP hs0 hs4
    obtain ⟨q, w, u, v, st, hu, hst, hn1, hm1, hu1, hp1, -, -⟩ := Replies.inter hn hR' hR
    have f1 : u.S = s - 1 := hS' _ hu
    have e1 : st.S = s := hS _ hst
    have hM : 1 ≤ st.M.prio := by
      have := (I.pair _ _ _ _ _ _ _ _ hn1 hm1 hu1).2 (by omega)
      exact Int.le_trans (I.A_pos hn1 f1) (le_prio this)
    have hmax : 1 ≤ (maxOf RecSt.M sts).prio :=
      Int.le_trans hM (le_prio (maxOf_ge RecSt.M hst))
    obtain ⟨st2, hst2, h⟩ := maxOf_mem RecSt.M hne
    obtain ⟨r2, v2, hm2, hp2, -⟩ := Replies.mem hR hst2
    rw [h] at hmax ⊢
    exact I.M_real hm2 hp2 hmax
  · exact I.real _ _ _ _ _ hP

theorem Inv.step_nonrec (hag : ∀ j a b, Ev.decide j a ∈ W → Ev.decide j b ∈ W → a = b)
    {x : Ev} (hs : Step n e W x) (hrec : ∀ r i s v st, x ≠ .record r i s v st) :
    Inv n e (W ++ [x]) := by
  cases hs with
  | init i me ids lead h1 h2 h3 _ =>
    refine I.extend _ ?_ ?_ ?_ ?_ hrec
    · intro i' me' a l h; cases h
      refine ⟨h1, h2, fun hl => ⟨h3 hl, fun me' b hb => ?_⟩⟩
      exact leaderOk_unique hag (I.lok _ _ _ hb) (h3 hl)
    · intro _ _ _ _ h; cases h
    · intro _ _ h; cases h
    · intro _ _ _ _ _ h; cases h
  | start i me tid ids lead h1 =>
    refine I.extend _ ?_ ?_ ?_ ?_ hrec
    · intro _ _ _ _ h; cases h
    · intro _ _ _ _ h; cases h
    · intro _ _ h; cases h
    · intro i' me' l t P h; cases h
      refine ⟨by omega, ⟨show (1:Int) ≤ hi by unfold hi; omega, Int.le_refl _, lead, h1⟩,
        fun hl _ _ => hl ▸ h1, fun _ h => absurd rfl h⟩
  | send i me lead s P v h1 h2 =>
    refine I.extend _ ?_ ?_ ?_ ?_ hrec
    · intro _ _ _ _ h; cases h
    · intro _ _ _ _ h; cases h; exact ⟨lead, P, h1, h2⟩
    · intro _ _ h; cases h
    · intro _ _ _ _ _ h; cases h
  | record => exact absurd rfl (hrec _ _ _ _ _)
  | fast i me lead s P sts st0 h1 h2 h3 h4 h5 =>
    refine I.extend _ ?_ ?_ ?_ ?_ hrec
    · intro _ _ _ _ h; cases h
    · intro _ _ _ _ h; cases h
    · intro _ _ h; cases h; exact .fast i me lead s P sts st0 h1 h2 h3 h4 h5
    · intro _ _ _ _ _ h; cases h
  | slow i me lead s P sts h1 h2 h3 h4 h5 =>
    refine I.extend _ ?_ ?_ ?_ ?_ hrec
    · intro _ _ _ _ h; cases h
    · intro _ _ _ _ h; cases h
    · intro _ _ h; cases h; exact .slow i me lead s P sts h1 h2 h3 h4 h5
    · intro _ _ _ _ _ h; cases h
  | next i me lead s P sts h1 h2 h3 =>
    refine I.extend _ ?_ ?_ ?_ ?_ hrec
    · intro _ _ _ _ h; cases h
    · intro _ _ _ _ h; cases h
    · intro _ _ h; cases h
    · intro i' me' l t P' h; cases h
      obtain ⟨st1, hst1⟩ := List.exists_mem_of_ne_nil sts (Replies.ne hn h2)
      obtain ⟨r1, v1, hm1, hp1, -⟩ := Replies.mem h2 hst1
      have e1 : st1.S = s := h3 _ hst1
      have hs4 : 4 ≤ s := by
        rcases I.sent_low (I.rec_sf hm1 hp1).1 with h | h <;> omega
      have hreal := I.next_real hn h1 h2 h3
      unfold nextVal at hreal
      unfold wrapInc
      split
      · refine ⟨by omega, hreal, fun _ h => by omega, fun h => by omega⟩
      · refine ⟨by omega, hreal, fun _ h => by omega, fun _ _ => ?_⟩
        refine ⟨me, lead, P, sts, by simpa using h1, by simpa using h2, by simpa using h3, ?_⟩
        simp only [Int.add_sub_cancel]; unfold nextVal; exact sim_refl _ _
  | adopt i me lead s P sts st h1 h2 h3 h4 =>
    refine I.extend _ ?_ ?_ ?_ ?_ hrec
    · intro _ _ _ _ h; cases h
    · intro _ _ _ _ h; cases h
    · intro _ _ h; cases h
    · intro i' me' l t P' h; cases h
      obtain ⟨r, v, hm, hpos, -⟩ := Replies.mem h2 h3
      have hF := (I.rec_sf hm hpos).1
      obtain ⟨me1, l1, P1, hP1, hv1⟩ := I.sent_ps hF
      refine ⟨I.low _ _ _ _ _ hP1, I.sent_real hF, ?_, ?_⟩
      · intro _ h4' hhi
        rw [h4'] at hF; exact I.sent4hi hF hhi
      · intro ht ht4
        obtain ⟨me'', l'', Q, sts', a1, a2, a3, a4⟩ := I.norm _ _ _ _ _ hP1 ht ht4
        exact ⟨me'', l'', Q, sts', a1, a2, a3, sim_trans (variants_sim hv1) a4⟩

end inv

end AgreeInv
namespace AgreeInv

theorem below_refl (c : RecSt) : Below c c :=
  ⟨Int.le_refl _, fun _ => ⟨rfl, rfl, le_refl _⟩, fun _ h => by omega⟩

theorem below_esp {st c : RecSt} (s : Int) (v : Val) (h : Below st c) :
    Below st (espStep c s v) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold espStep
  split
  · exact ⟨h1, fun e => let ⟨a, b, c'⟩ := h2 e; ⟨a, b, le_trans c' (le_recMax_left _ _)⟩, h3⟩
  split
  · rename_i hlt
    refine ⟨by simp; omega, fun e => by simp at e; omega, fun _ e => ?_⟩
    simp at e ⊢
    have : st.S = c.S := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact (h2 this).2.2
  · exact ⟨h1, h2, h3⟩

theorem esp_props (c : RecSt) (s : Int) (v : Val) (hc : 0 ≤ c.S) :
    0 ≤ (espStep c s v).S ∧ s ≤ (espStep c s v).S ∧ ((espStep c s v).S = s → le v (espStep c s v).A) := by
  unfold espStep
  split
  · rename_i h; exact ⟨hc, by simp; omega, fun _ => le_recMax_right _ _⟩
  split
  · exact ⟨by simp; omega, by simp, fun _ => le_refl _⟩
  · exact ⟨hc, by omega, fun h => by omega⟩

theorem esp_SF {W i} (c : RecSt) (s : Int) (v : Val) (hc : SF W i c) (hc0 : 0 ≤ c.S)
    (hv : sentAt W i s v) (hs : s ≠ 0) : SF W i (espStep c s v) := by
  unfold espStep
  split
  · rename_i h
    rcases hc with hc | ⟨a1, a2, a3, a4⟩
    · subst hc; simp [RecSt.init] at h; omega
    · refine .inr ⟨a1, a2, ?_, a4⟩
      rcases recMax_cases c.A v with e | e <;> rw [e]
      · exact a3
      · rw [h]; exact hv
  split
  · rename_i h0 h1
    refine .inr ⟨by simp; omega, hv, hv, ?_⟩
    simp only
    split
    · exact .inl rfl
    · rcases hc with hc | ⟨_, _, a3, _⟩
      · subst hc; exact .inl rfl
      · exact .inr (by have : s - 1 = c.S := by omega
                       rw [this]; exact a3)
  · exact hc

section inv
variable {n e : Int} {W : World} (I : Inv n e W)
include I

theorem Inv.st_nonneg {r i s v st} (h : Ev.record r i s v st ∈ W) : 0 ≤ st.S := by
  rcases (I.recs _ _ _ _ _ h).2.1 with h' | h'
  · subst h'; simp [RecSt.init]
  · omega

theorem Inv.step_rec {r i me s v c} (hsend : Ev.send i me s v ∈ W) (hc : recState W r i = c) :
    Inv n e (W ++ [.record r i s v (espStep c s v)]) := by
  have hW := sub_snoc W (.record r i s v (espStep c s v))
  have hv : sentAt W i s v := ⟨me, hsend⟩
  have hs0 : s ≠ 0 := by have := I.sent_low hv; omega
  have hcur : ∀ r' i', recState (W ++ [.record r i s v (espStep c s v)]) r' i' =
      if r = r' ∧ i = i' then espStep c s v else recState W r' i' := by
    intro r' i'; rw [recState_snoc]
  have hc' := esp_props c s v (hc ▸ (I.cur r i).1)
  have hsf := esp_SF c s v (hc ▸ (I.cur r i).2) (hc ▸ (I.cur r i).1) hv hs0
  constructor
  · intro i me a b la lb ha hb
    rcases mem_snoc.1 ha with ha | ha
    · rcases mem_snoc.1 hb with hb | hb
      · exact I.uniq _ _ _ _ _ _ ha hb
      · cases hb
    · cases ha
  · intro i me a l ha
    rcases mem_snoc.1 ha with ha | ha
    · exact I.ne _ _ _ _ ha
    · cases ha
  · intro i me a ha
    rcases mem_snoc.1 ha with ha | ha
    · exact leaderOk.mono hW (I.lok _ _ _ ha)
    · cases ha
  · intro i me me' a b ha hb
    rcases mem_snoc.1 ha with ha | ha
    · rcases mem_snoc.1 hb with hb | hb
      · exact I.lu _ _ _ _ _ ha hb
      · cases hb
    · cases ha
  · intro i me s v h
    rcases mem_snoc.1 h with h | h
    · obtain ⟨l, P, h1, h2⟩ := I.send _ _ _ _ h; exact ⟨l, P, hW _ h1, h2⟩
    · cases h
  · intro i a h
    rcases mem_snoc.1 h with h | h
    · exact Step.decide_mono hW (I.dec _ _ h)
    · cases h
  · intro i me l t P h
    rcases mem_snoc.1 h with h | h
    · exact I.low _ _ _ _ _ h
    · cases h
  · intro i me l t P h
    rcases mem_snoc.1 h with h | h
    · exact (I.real _ _ _ _ _ h).mono hW
    · cases h
  · intro i me P h hhi
    rcases mem_snoc.1 h with h | h
    · exact hW _ (I.lead _ _ _ h hhi)
    · cases h
  · intro i me l t P h h1 h2
    rcases mem_snoc.1 h with h | h
    · exact (I.norm _ _ _ _ _ h h1 h2).mono hW
    · cases h
  · intro r' i'; rw [hcur]
    split
    · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; exact ⟨hc'.1, hsf.mono hW⟩
    · exact ⟨(I.cur r' i').1, (I.cur r' i').2.mono hW⟩
  · intro r' i' s' v' st h
    rw [RecOK, hcur]
    rcases mem_snoc.1 h with h | h
    · obtain ⟨h1, h2, h3, h4, h5⟩ := I.recs _ _ _ _ _ h
      refine ⟨h1.mono hW, h2.mono hW, h3, h4, ?_⟩
      split
      · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; rw [hc] at h5; exact below_esp s v h5
      · exact h5
    · cases h
      exact ⟨hv.mono hW, hsf.mono hW, hc'.2.1, hc'.2.2, by simp only [and_self, ite_true]; exact below_refl _⟩
  · intro r' i' s1 v1 st1 s2 v2 st2 h1 h2 hpos
    have old : ∀ s1 v1 st1, Ev.record r i s1 v1 st1 ∈ W → Below st1 (espStep c s v) :=
      fun _ _ _ h => below_esp s v (hc ▸ (I.recs _ _ _ _ _ h).2.2.2.2)
    rcases mem_snoc.1 h1 with h1 | h1 <;> rcases mem_snoc.1 h2 with h2 | h2
    · exact I.pair _ _ _ _ _ _ _ _ h1 h2 hpos
    · cases h2
      obtain ⟨-, b2, b3⟩ := old _ _ _ h1
      exact ⟨fun e => let ⟨x, y, _⟩ := b2 e; ⟨x, y⟩, b3 hpos⟩
    · cases h1
      obtain ⟨b1, b2, -⟩ := old _ _ _ h2
      exact ⟨fun e => let ⟨x, y, _⟩ := b2 e.symm; ⟨x.symm, y.symm⟩, fun e => by omega⟩
    · cases h1; cases h2
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun e => by omega⟩

end inv

end AgreeInv
namespace AgreeInv

/-- Every proposer at step `t` holds a value with ids `X`. -/
def Good (W : World) (i : Int) (X : List GoString) (t : Int) : Prop :=
  ∀ me l P, Ev.pstate i me l t P ∈ W → P.ids = X

theorem variants_id {l s P v} (hs : s.tmod 4 ≠ 0) (h : variants l s P v) : v = P :=
  (variants_sim h).2.2.2 hs

section inv
variable {n e : Int} {W : World} (I : Inv n e W) (hn : 1 ≤ n)
include I hn

omit hn in
theorem Inv.sent_good {i X t v} (g : Good W i X t) (h : sentAt W i t v) : v.ids = X := by
  obtain ⟨me, l, P, h1, h2⟩ := I.sent_ps h
  rw [(variants_sim h2).2.2.1]; exact g _ _ _ h1

theorem Inv.good_step {i X t} (ht : 4 ≤ t) (g : Good W i X t)
    (g3 : t.tmod 4 = 3 → Good W i X (t - 1)) : Good W i X (t + 1) := by
  intro me l P hP
  obtain ⟨me', l', Q, sts, hQ, hR, hS, hsim⟩ := I.norm _ _ _ _ _ hP (by omega) (by omega)
  simp only [Int.add_sub_cancel] at hQ hR hS hsim
  rw [hsim.2.2.1]
  have hne : P.ids ≠ [] := I.real_ne (I.real _ _ _ _ _ hP)
  rw [hsim.2.2.1] at hne
  have hsne := Replies.ne hn hR
  unfold nextVal at hne ⊢
  split
  · obtain ⟨st, hst, h⟩ := maxOf_mem RecSt.F hsne
    obtain ⟨r, v, hm, hp, -⟩ := Replies.mem hR hst
    rw [h]
    have := (I.rec_sf hm hp).1; rw [hS _ hst] at this; exact I.sent_good g this
  rename_i h0
  split
  · rename_i h3
    rw [ite_eq_right_of_eq_false _ _ (eq_false h0), ite_eq_left_of_eq_true _ _ (eq_true h3)] at hne
    obtain ⟨st, hst, h⟩ := maxOf_mem RecSt.M hsne
    obtain ⟨r, v, hm, hp, -⟩ := Replies.mem hR hst
    rw [h] at hne ⊢
    rcases (I.rec_sf hm hp).2.2 with h' | h'
    · rw [h'] at hne; simp [Val.bot] at hne
    · rw [hS _ hst] at h'; exact I.sent_good (g3 h3) h'
  · exact g _ _ _ hQ

theorem Inv.good_from {i X t0} (h4 : 4 ≤ t0) (h3 : t0.tmod 4 ≠ 3) (g : Good W i X t0) :
    ∀ t, t0 ≤ t → Good W i X t := by
  have key : ∀ k : Nat, ∀ m : Nat, m ≤ k → Good W i X (t0 + m) := by
    intro k
    induction k with
    | zero => intro m hm; have : m = 0 := by omega
              subst this; simpa using g
    | succ k ih =>
      intro m hm
      by_cases hmn : m ≤ k
      · exact ih m hmn
      have : m = k + 1 := by omega
      subst this
      have e : t0 + ((k + 1 : Nat) : Int) = (t0 + k) + 1 := by omega
      rw [e]
      refine I.good_step hn (by omega) (ih k (Nat.le_refl _)) (fun h => ?_)
      have hk : k ≠ 0 := by
        intro hk; subst hk; simp at h; exact h3 h
      have e' : t0 + (k : Int) - 1 = t0 + ((k - 1 : Nat) : Int) := by omega
      rw [e']; exact ih _ (by omega)
  intro t ht
  have := key (t - t0).toNat _ (Nat.le_refl _)
  rwa [show t0 + ((t - t0).toNat : Int) = t by omega] at this

theorem Inv.fast_info {i me l s P sts st0} (hP : Ev.pstate i me l s P ∈ W)
    (hR : Replies n W i l s P sts) (h0 : s.tmod 4 = 0) (h4 : ∀ st ∈ sts, st.S = s ∧ st.F.prio = hi)
    (h5 : sts.head? = some st0) :
    (∃ me0, Ev.init i me0 st0.F.ids true ∈ W) ∧ ∀ t, 5 ≤ t → Good W i st0.F.ids t := by
  have hst0 : st0 ∈ sts := List.mem_of_head? h5
  obtain ⟨e0, f0⟩ := h4 st0 hst0
  obtain ⟨r0, v0, hm0, hp0, -⟩ := Replies.mem hR hst0
  have hF0 := (I.rec_sf hm0 hp0).1
  rw [e0] at hF0
  have hs4 : s = 4 := by
    rcases I.sent_low hF0 with h | h
    · omega
    apply Classical.byContradiction; intro hne4
    obtain ⟨me1, l1, P1, -, hv1⟩ := I.sent_ps hF0
    unfold variants at hv1
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h0, .inl (by omega)⟩)] at hv1
    have := hv1.1.2; rw [f0] at this; unfold hi at this; omega
  subst hs4
  have hreal0 := I.sent_real hF0
  have hinit0 := I.sent4hi hF0 f0
  refine ⟨⟨_, hinit0⟩, I.good_from hn (by omega) (by decide) ?_⟩
  intro me' l' P' hP'
  obtain ⟨me'', l'', Q, sts', -, hR', hS', hsim⟩ := I.norm _ _ _ _ _ hP' (by omega) (by omega)
  rw [hsim.2.2.1]
  simp only [show (5 : Int) - 1 = 4 by rfl] at hR' hS'
  have hnv : nextVal (5 - 1) Q sts' = maxOf RecSt.F sts' := by
    unfold nextVal; simp
  rw [hnv]
  -- the replies share a recorder with the fast path's
  obtain ⟨q, w, st, w', u, hst, hu, hq1, hq2, hpst, hpu, -, -⟩ := Replies.inter hn hR hR'
  have hu4 : u.S = 4 := hS' _ hu
  have huF : u.F.prio = hi := by
    have := ((I.pair _ _ _ _ _ _ _ _ hq1 hq2 hpst).1 (by rw [(h4 st hst).1, hu4])).1
    rw [← this]; exact (h4 st hst).2
  have hge : hi ≤ (maxOf RecSt.F sts').prio := by
    rw [← huF]; exact le_prio (maxOf_ge RecSt.F hu)
  have hsent : sentAt W i 4 (maxOf RecSt.F sts') := by
    obtain ⟨u2, hu2, h⟩ := maxOf_mem RecSt.F (Replies.ne hn hR')
    obtain ⟨r2, v2, hm2, hp2, -⟩ := Replies.mem hR' hu2
    rw [h]; have := (I.rec_sf hm2 hp2).1; rwa [hS' _ hu2] at this
  have hr := I.sent_real hsent
  have hhi : (maxOf RecSt.F sts').prio = hi := by have := hr.2.1; omega
  have hinit := I.sent4hi hsent hhi
  have hpid := I.lu _ _ _ _ _ hinit hinit0
  rw [hpid] at hinit
  exact (I.uniq _ _ _ _ _ _ hinit hinit0).1

theorem Inv.slow_info {i me l s P sts} (hP : Ev.pstate i me l s P ∈ W)
    (hR : Replies n W i l s P sts) (h2 : s.tmod 4 = 2) (h4 : ∀ st ∈ sts, st.S = s)
    (h5 : (maxOf RecSt.M sts).tagEq P) :
    6 ≤ s ∧ (∀ me' l' P', Ev.pstate i me' l' s P' ∈ W → le P' P) ∧
      ∀ t, s + 2 ≤ t → Good W i P.ids t := by
  have hsne := Replies.ne hn hR
  obtain ⟨st0, hst0⟩ := List.exists_mem_of_ne_nil sts hsne
  obtain ⟨r0, v0, -, hp0, -⟩ := Replies.mem hR hst0
  have hs0 : 0 < s := h4 _ hst0 ▸ hp0
  have hs6 : 6 ≤ s := by
    have := I.low _ _ _ _ _ hP
    rw [tmod_pos (by omega)] at h2; omega
  have hsm : (s - 1).tmod 4 = 1 := by rw [tmod_pos (by omega)] at h2 ⊢; omega
  have hs4 : s ≠ 4 := by omega
  have hsn : s.tmod 4 ≠ 0 := by omega
  have hPreal := I.real _ _ _ _ _ hP
  have hMP : le (maxOf RecSt.M sts) P := le_of_tagEq h5
  -- every value at step `s` is at most `P`
  have allLe : ∀ me' l' P', Ev.pstate i me' l' s P' ∈ W → le P' P := by
    intro me' l' P' hP'
    obtain ⟨me'', l'', Q, sts', -, hR', hS', hsim⟩ := I.norm _ _ _ _ _ hP' hs0 hs4
    have hPQ : P' = Q := by
      have := hsim.2.2.2 hsn; rw [this]; unfold nextVal; simp [hsm]
    subst hPQ
    obtain ⟨q, w, u, v, st, hu, hst, hn1, hm1, hu1, -, hw1, -⟩ := Replies.inter hn hR' hR
    rw [variants_id (by omega) hw1] at hn1
    have f1 : u.S = s - 1 := hS' _ hu
    have e1 : st.S = s := h4 _ hst
    have b1 := (I.recs _ _ _ _ _ hn1).2.2.2.1 f1
    have b2 := (I.pair _ _ _ _ _ _ _ _ hn1 hm1 hu1).2 (by omega)
    exact le_trans b1 (le_trans b2 (le_trans (maxOf_ge RecSt.M hst) hMP))
  refine ⟨hs6, allLe, I.good_from hn (by omega) (by rw [tmod_pos (by omega)] at h2 ⊢; omega) ?_⟩
  intro me2 l2 P2 hP2
  obtain ⟨me'', l'', Q, sts', -, hR', hS', hsim⟩ := I.norm _ _ _ _ _ hP2 (by omega) (by omega)
  have e3 : s + 2 - 1 = s + 1 := by omega
  rw [e3] at hR' hS' hsim
  have hs3 : (s + 1).tmod 4 = 3 := by rw [tmod_pos (by omega)] at h2 ⊢; omega
  have hnv : nextVal (s + 1) Q sts' = maxOf RecSt.M sts' := by
    unfold nextVal; simp [hs3]
  rw [hsim.2.2.1, hnv]
  -- `P` is below the maximum
  have hlo : le P (maxOf RecSt.M sts') := by
    obtain ⟨q, w, st, w', u, hst, hu, hq1, hq2, hpst, -, hw, -⟩ := Replies.inter hn hR hR'
    rw [variants_id hsn hw] at hq1
    have b1 := (I.recs _ _ _ _ _ hq1).2.2.2.1 (h4 _ hst)
    have b2 := (I.pair _ _ _ _ _ _ _ _ hq1 hq2 hpst).2 (by rw [h4 _ hst, hS' _ hu])
    exact le_trans b1 (le_trans b2 (maxOf_ge RecSt.M hu))
  -- and above it
  have hup : le (maxOf RecSt.M sts') P := by
    obtain ⟨u, hu, h⟩ := maxOf_mem RecSt.M (Replies.ne hn hR')
    obtain ⟨q, w, a1, hpu, -⟩ := Replies.mem hR' hu
    rw [h]
    rcases (I.rec_sf a1 hpu).2.2 with h | h
    · rw [h]; exact bot_le hPreal.1
    · rw [hS' _ hu, Int.add_sub_cancel] at h
      obtain ⟨me3, l3, P3, hP3, hv3⟩ := I.sent_ps h
      rw [variants_id hsn hv3]; exact allLe _ _ _ hP3
  have heq := tagEq_of_le hup hlo
  have hreal : Real W i (maxOf RecSt.M sts') := by
    have hp : 1 ≤ (maxOf RecSt.M sts').prio := by rw [heq.1]; exact hPreal.1
    obtain ⟨u, hu, h⟩ := maxOf_mem RecSt.M (Replies.ne hn hR')
    obtain ⟨q, w, a1, hpu, -⟩ := Replies.mem hR' hu
    rw [h] at hp ⊢
    exact I.M_real a1 hpu hp
  exact I.real_ids hreal hPreal heq.2.1

/-- What a decision says. -/
theorem Inv.decide_info {i a} (h : Ev.decide i a ∈ W) :
    ((∃ me0, Ev.init i me0 a true ∈ W) ∧ ∀ t, 5 ≤ t → Good W i a t) ∨
    (∃ s me l P, a = P.ids ∧ Ev.pstate i me l s P ∈ W ∧ 6 ≤ s ∧ s.tmod 4 = 2 ∧
      (∀ me' l' P', Ev.pstate i me' l' s P' ∈ W → le P' P) ∧ ∀ t, s + 2 ≤ t → Good W i P.ids t) := by
  cases I.dec _ _ h with
  | fast _ me l s P sts st0 h1 h2 h3 h4 h5 => exact .inl (I.fast_info hn h1 h2 h3 h4 h5)
  | slow _ me l s P sts h1 h2 h3 h4 h5 =>
    obtain ⟨a1, a2, a3⟩ := I.slow_info hn h1 h2 h3 h4 h5
    exact .inr ⟨s, me, l, P, rfl, h1, a1, h3, a2, a3⟩

theorem Inv.decide_init {i a} (h : Ev.decide i a ∈ W) : ∃ me l, Ev.init i me a l ∈ W := by
  rcases I.decide_info hn h with ⟨⟨me0, h1⟩, -⟩ | ⟨s, me, l, P, rfl, hP, -⟩
  · exact ⟨_, _, h1⟩
  · obtain ⟨l', h'⟩ := (I.real _ _ _ _ _ hP).2.2; exact ⟨_, _, h'⟩

theorem Inv.agree {i a b} (ha : Ev.decide i a ∈ W) (hb : Ev.decide i b ∈ W) : a = b := by
  have slow_later : ∀ s1 me1 l1 P1 s2 me2 l2 P2, Ev.pstate i me1 l1 s1 P1 ∈ W →
      Ev.pstate i me2 l2 s2 P2 ∈ W →
      (∀ me' l' P', Ev.pstate i me' l' s1 P' ∈ W → le P' P1) →
      (∀ t, s1 + 2 ≤ t → Good W i P1.ids t) →
      (∀ me' l' P', Ev.pstate i me' l' s2 P' ∈ W → le P' P2) →
      (∀ t, s2 + 2 ≤ t → Good W i P2.ids t) →
      s1.tmod 4 = 2 → s2.tmod 4 = 2 → 6 ≤ s1 → 6 ≤ s2 → P1.ids = P2.ids := by
    intro s1 me1 l1 P1 s2 me2 l2 P2 h1 h2 x1 g1 x2 g2 t1 t2 _ _
    rw [tmod_pos (by omega)] at t1 t2
    rcases Int.lt_trichotomy s1 s2 with h | h | h
    · exact (g1 s2 (by omega) _ _ _ h2).symm
    · subst h
      have := tagEq_of_le (x2 _ _ _ h1) (x1 _ _ _ h2)
      exact I.real_ids (I.real _ _ _ _ _ h1) (I.real _ _ _ _ _ h2) this.2.1
    · exact g2 s1 (by omega) _ _ _ h1
  rcases I.decide_info hn ha with ⟨⟨ma, ia⟩, ga⟩ | ⟨s1, me1, l1, P1, rfl, h1, x1, t1, y1, g1⟩ <;>
    rcases I.decide_info hn hb with ⟨⟨mb, ib⟩, gb⟩ | ⟨s2, me2, l2, P2, rfl, h2, x2, t2, y2, g2⟩
  · have := I.lu _ _ _ _ _ ia ib; subst this
    exact (I.uniq _ _ _ _ _ _ ia ib).1
  · exact (ga s2 (by omega) _ _ _ h2).symm
  · exact gb s1 (by omega) _ _ _ h1
  · exact slow_later _ _ _ _ _ _ _ _ h1 h2 y1 g1 y2 g2 t1 t2 x1 x2

end inv

theorem inv_of_reach {n e : Int} {W : World} (hn : 1 ≤ n) (h : Reach n e W) : Inv n e W := by
  induction h with
  | nil =>
    constructor <;> intros <;> simp_all [recState, RecSt.init, SF]
  | step W x _ hs I =>
    cases x with
    | record r i s v st => cases hs with | record _ _ me _ _ h => exact I.step_rec h rfl
    | _ => exact I.step_nonrec hn (fun _ _ _ ha hb => I.agree hn ha hb) hs (by intros; simp)

end AgreeInv

/-- **Agreement** (the protocol's safety): in a reachable history, the decisions of a slot are
one nonempty list of batch ids, which some proxy proposed for that slot (package `pure`). -/
theorem agreement {n e : Int} {W : World} (hn : 1 ≤ n) (h : Reach n e W) :
    (∀ i a b, Ev.decide i a ∈ W → Ev.decide i b ∈ W → a = b) ∧
    (∀ i a, Ev.decide i a ∈ W → a ≠ []) ∧
    (∀ i a, Ev.decide i a ∈ W → ∃ me lead, Ev.init i me a lead ∈ W) := by
  have I := AgreeInv.inv_of_reach hn h
  refine ⟨fun i a b ha hb => I.agree hn ha hb, fun i a ha => ?_, fun i a ha => I.decide_init hn ha⟩
  obtain ⟨me, l, h⟩ := I.decide_init hn ha
  exact I.ne _ _ _ _ h

/-- An `init` at a summary slot proposes one summary of a permutation (package `pure`). -/
theorem init_summary {n e : Int} {W : World} (h : Reach n e W) {i me : Int} {ids : List GoString}
    {lead : Bool} (hin : Ev.init i me ids lead ∈ W) (hs : sumSlot n e i) :
    ∃ p, isPerm n.toNat p ∧ ids = [summaryId p] := by
  induction h with
  | nil => simp at hin
  | step W x _ hs ih =>
    rcases List.mem_append.1 hin with h' | h'
    · exact ih h'
    · simp only [List.mem_singleton] at h'
      subst h'
      cases hs with
      | init _ _ _ _ _ _ _ h4 => exact h4 hs

/-- One leader per slot: two `init`s of a slot with the leader flag are by the same replica
(package `pure`). -/
theorem lead_unique {n e : Int} {W : World} (hn : 1 ≤ n) (h : Reach n e W) {i me me' : Int}
    {a b : List GoString} (ha : Ev.init i me a true ∈ W) (hb : Ev.init i me' b true ∈ W) :
    me = me' := by
  exact (AgreeInv.inv_of_reach hn h).lu _ _ _ _ _ ha hb

/-- The slot of an event. -/
def Ev.slot : Ev → Int
  | .init i _ _ _ => i
  | .pstate i _ _ _ _ => i
  | .send i _ _ _ => i
  | .record _ i _ _ _ => i
  | .decide i _ => i

/-- Every event's slot was proposed by some proxy (`init`) (package `pure`). -/
theorem slots_inited {n e : Int} {W : World} (hn : 1 ≤ n) (h : Reach n e W) :
    ∀ ev ∈ W, ∃ me ids lead, Ev.init ev.slot me ids lead ∈ W := by
  have I := AgreeInv.inv_of_reach hn h
  intro ev he
  cases ev with
  | init i me ids lead => exact ⟨me, ids, lead, he⟩
  | pstate i me l s P =>
    obtain ⟨l', h'⟩ := (I.real _ _ _ _ _ he).2.2; exact ⟨_, _, l', h'⟩
  | send i me s v =>
    obtain ⟨l', h'⟩ := (I.sent_real ⟨me, he⟩).2.2; exact ⟨_, _, l', h'⟩
  | record r i s v st =>
    obtain ⟨l', h'⟩ := (I.sent_real (I.recs _ _ _ _ _ he).1).2.2; exact ⟨_, _, l', h'⟩
  | decide i a => obtain ⟨me, l, h'⟩ := I.decide_init hn he; exact ⟨me, a, l, h'⟩

end Perennial.raxos.pure
