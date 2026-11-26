/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: which kind of `ready` report a `Ready` is (#33 S4)

The raft side of `antSim_ready` (`notes/antithesis-rawnode-design.md` §3.3, "guard by guard"):
`ready_kind` classifies a reported `Ready` (`Reported`) taken at the state `ps₁` the node reached
(`Reach`) into the kinds `OnDisk`/`InMemory` are evaluated for (`ReadyKind`), each with the
protocol facts its evaluation reads: a campaign (`TickEndO`'s, the next term and the node's own
vote); a vote granted, at the node's term or with the request's term adopted; a term adopted
only (`PreEndO`'s, at the message's term); a role change only (a candidate back to a follower at
its term: a lost election or `padoptLeader`); a follower's store and/or commit on a `MsgApp` (its
entries from the first conflict on, `plogMaybeAppend`, its commit within `min(m.commit,
lastnewi)`); a follower's commit on a heartbeat (to `m.commit`); a leader's win (the tally a
quorum, the empty entry of its term appended), proposal (entries of its term appended at its
end), or commit (`cmt`: a quorum of `Match` at an entry of its term).

What the classification shows on the way (the design's hand-checked claims): a term changes only
by a campaign (`camp`, the next term, from `TickEndO`) or by the preamble (`grant`, `adopt`,
`store`, `hb`: the handled message's term, higher than the node's); a win is at the node's own
term (so no term change and a win in one input); `Reach.stay` is never reported (`stay_quiet`); a
drain's later `Ready` (`Reach.advance`) changes no term or vote (`AdvanceEndO` steps only
self-addressed messages of the node's term).

`selfOut_reach`: the self-addressed messages in the outbox at a `Ready`'s state are a leader's
self-acknowledgement (`pselfAck`, at its term and last index, `reject = false`) or a candidate's
self-vote (at its term, `reject = false`); `qs_self` reads them off `ReadyOutP`'s `qs`.

The facts taken from the relation are explicit hypotheses (the view's outbox empty, its base,
the leader hint, a non-follower's vote its own, the received message's shape), so these lemmas
do not depend on the relation's exact shape.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Outbox

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

section kind
variable [GooseExts]
variable {cf : CfgM} {N : Nat} {kk : NodeK}

/-! ## The protocol reading of a `Ready` below `mskB1a` -/

/-- **`ReadyOutP` read on the protocol state** (parity B1, below `mskB1a`: sync, no snapshot, no
ghost prefix, the disk raft's own state): the `Ready` at `ps` from the view `v` reports `ps`'s role
and hard state, its entries cut `v.ps.log` (the view's log, which is its disk's), its
self-addressed messages and those to others are `ps`'s outbox split by destination, its committed
entries follow what was handed out, `ps`'s base is `base0` and its log's indices its positions. -/
def ReadyOutO (N : Nat) (id : w64) (v : NodeView) (ps : PState) (rd : ReadyD) : Prop :=
  rd.role = ps.role ∧ rd.term = ps.term ∧ rd.vote = ps.vote ∧ rd.commit = ps.commit ∧
  (rd.ents = [] → ps.log = v.ps.log) ∧
  (∀ e0 ∈ rd.ents.head?, ps.log = v.ps.log.take (uint.nat e0.Index' - 1) ++ rd.ents ∧
    ∀ e ∈ v.ps.log[uint.nat e0.Index' - 1]?, e.Term' ≠ e0.Term') ∧
  rd.qs.Perm (ps.outbox.filter (fun q => decide (q.dst = id))) ∧
  rd.msgs.Perm (ps.outbox.filter (fun q => decide (q.dst ≠ id))) ∧
  v.delivered ++ rd.ce <+: ps.log ∧ (v.delivered ++ rd.ce).length ≤ uint.nat ps.commit ∧
  ps.base = base0 ∧ LogIdx ps.log ∧ ReadyMsgsToVoters N rd

/-- **`Reported` read on the protocol state**: the `Ready`'s hard state, entries or role differ
from the view's. -/
def ReportedO (v : NodeView) (rd : ReadyD) : Prop :=
  rd.term ≠ v.ps.term ∨ rd.vote ≠ v.ps.vote ∨ rd.commit ≠ v.ps.commit ∨ rd.ents ≠ [] ∨
    rd.role ≠ v.ps.role

/-- `ReadyOutP` below `mskB1a` (sync, snapshots off, no ghost prefix before or after, the disk's log
the view's full log) is its protocol reading. -/
theorem readyOutO_of {R : RunCfg} {n : Fin R.N} {v : NodeView} {r : RState}
    {rd : ReadyD} (h : ReadyOutP R n v r rd) (hasync : R.md.async = false)
    (hsn : R.md.snapshots = false) (hdl : v.dur.log = v.ps.log) (hfp : r.fp = []) :
    ReadyOutO R.N (nodeId n) v r.p rd := by
  obtain ⟨hR, -, hT, hV, hC, hnil, hfst, hqp, hsync, -, -, hpfx, hlen, -, hsnapC, hidx, hvot⟩ := h
  have hfull : r.full = r.p.log := by unfold RState.full; rw [hfp]; rfl
  obtain ⟨hb0, hsn0, -⟩ := hsnapC hsn
  rw [hfull, hdl] at hnil hfst
  rw [hfull] at hpfx hidx
  exact ⟨hR, hT, hV, hC, hnil hsn0, hfst, hqp, (hsync hasync).2, hpfx, hlen, hb0, hidx, hvot⟩

/-- `Reported` below `mskB1a` (the disk raft's own state, no snapshot, no pre-candidate) is its
protocol reading. -/
theorem reportedO_of {v : NodeView} {rd : ReadyD} (h : Reported v rd) (hdur : v.dur = durOf v.r)
    (hsn : rd.snap = none) (hpre : rd.pre = false) (hvp : v.pre = false) : ReportedO v rd := by
  unfold Reported at h
  rw [hdur, hpre] at h
  unfold roleS at h
  rw [hvp] at h
  rcases h with h | h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact absurd hsn h
  · exact .inr (.inr (.inr (.inr fun he => h (by rw [he]))))

/-! ## The `Ready`'s entries from its log -/

theorem getElem?_take_append_lt {L Y : List EntryM} {k j : Nat} (hj : j < k) (hk : k ≤ L.length) :
    (L.take k ++ Y)[j]? = L[j]? := by
  rw [List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take]
  simp [hj]

theorem getElem?_take_append_eq {L Y : List EntryM} {k : Nat} (hk : k ≤ L.length) :
    (L.take k ++ Y)[k]? = Y[0]? := by
  rw [List.getElem?_append_right (by rw [List.length_take]; omega)]
  simp [List.length_take, Nat.min_eq_left hk]

/-- A `Ready` whose log is unchanged writes no entries (`ReadyOutP`: its first entry starts at a
conflict with the durable log or past its end). -/
theorem ents_nil_of_log {id : w64} {v : NodeView} {ps : PState} {rd : ReadyD}
    (hro : ReadyOutO N id v ps rd) (hl : ps.log = v.ps.log) : rd.ents = [] := by
  obtain ⟨-, -, -, -, -, hfst, -⟩ := hro
  cases he : rd.ents with
  | nil => rfl
  | cons e0 es =>
    exfalso
    obtain ⟨hlog, hne⟩ := hfst e0 (by rw [he]; simp)
    rw [he, hl] at hlog
    by_cases ha : uint.nat e0.Index' - 1 < v.ps.log.length
    · have h1 : v.ps.log[uint.nat e0.Index' - 1]? = some e0 := by
        refine (congrArg (fun l : List EntryM => l[uint.nat e0.Index' - 1]?) hlog).trans ?_
        rw [getElem?_take_append_eq (Nat.le_of_lt ha)]; rfl
      exact hne e0 h1 rfl
    · have := congrArg List.length hlog
      simp only [List.length_append, List.length_take, List.length_cons] at this; omega

/-- **The `Ready`'s entries** when its log is the durable log `L0` cut at `k` (within it)
followed by `Y`, `Y` not starting with `L0`'s entry at `k`: they are `Y`. (`ReadyOutP` cuts at its
first entry's position, `LogIdx`; a different cut would put `L0`'s entry at the earlier one in the
other's first place.) -/
theorem ents_of_split {id : w64} {v : NodeView} {ps : PState} {rd : ReadyD}
    (hro : ReadyOutO N id v ps rd) {k : Nat} {y0 : EntryM} {ys : List EntryM}
    (hk : k ≤ v.ps.log.length) (hl : ps.log = v.ps.log.take k ++ y0 :: ys)
    (hY : v.ps.log[k]? ≠ some y0) : rd.ents = y0 :: ys := by
  obtain ⟨-, -, -, -, hnil, hfst, -, -, -, -, -, hidx, -⟩ := hro
  cases he : rd.ents with
  | nil =>
    exfalso
    have h1 := hnil he
    apply hY
    have h2 : (v.ps.log.take k ++ y0 :: ys)[k]? = some y0 := by rw [getElem?_take_append_eq hk]; rfl
    rw [← hl, h1] at h2; exact h2
  | cons e0 es =>
    obtain ⟨hlog, hne⟩ := hfst e0 (by rw [he]; simp)
    rw [he] at hlog
    generalize hL : v.ps.log = L at hk hl hY hlog hne
    generalize ha' : uint.nat e0.Index' - 1 = a at hlog hne
    -- `e0`'s position in the new log is its index less one (`LogIdx`), so the cut is within `L`.
    have hpos : ps.log[(L.take a).length]? = some e0 := by
      rw [hlog, List.getElem?_append_right (Nat.le_refl _)]; simp
    have hix := hidx _ _ hpos
    have hnat : ((uint.nat e0.Index' : Nat) : Int) = uint.Z e0.Index' := by word
    have hlt : (L.take a).length = a := by
      rw [List.length_take] at hix ⊢; omega
    have ha : a ≤ L.length := by rw [List.length_take] at hlt; omega
    rcases Nat.lt_trichotomy a k with hak | rfl | hka
    · exfalso
      have h1 : ps.log[a]? = L[a]? := by rw [hl]; exact getElem?_take_append_lt hak hk
      have h2 : ps.log[a]? = some e0 := by rw [hlog, getElem?_take_append_eq ha]; rfl
      exact hne e0 (h1.symm.trans h2) rfl
    · rw [hlog] at hl; exact List.append_cancel_left hl
    · exfalso
      have h1 : ps.log[k]? = L[k]? := by rw [hlog]; exact getElem?_take_append_lt hka ha
      have h2 : ps.log[k]? = some y0 := by rw [hl, getElem?_take_append_eq hk]; rfl
      exact hY (h1.symm.trans h2)

/-- A `Ready` whose log is the durable log with `es` appended writes `es`. -/
theorem ents_of_append {id : w64} {v : NodeView} {ps : PState} {rd : ReadyD}
    (hro : ReadyOutO N id v ps rd) {es : List EntryM} (hl : ps.log = v.ps.log ++ es) : rd.ents = es := by
  cases es with
  | nil => rw [List.append_nil] at hl; exact ents_nil_of_log hro hl
  | cons y0 ys =>
    refine ents_of_split hro (Nat.le_refl _) (by rw [List.take_length]; exact hl) ?_
    rw [List.getElem?_eq_none (Nat.le_refl _)]; simp

/-- **What a reported `Ready` changed** (`Reported`, its entries non-empty only when the log
changed): the term, the vote, the commit, the log or the role. -/
theorem reported_changed {id : w64} {v : NodeView} {ps : PState} {rd : ReadyD}
    (hro : ReadyOutO N id v ps rd) (hrep : ReportedO v rd) :
    ps.term ≠ v.ps.term ∨ ps.vote ≠ v.ps.vote ∨ ps.commit ≠ v.ps.commit ∨ ps.log ≠ v.ps.log ∨
      ps.role ≠ v.ps.role := by
  obtain ⟨hr, ht, hv, hc, -⟩ := _root_.id hro
  rcases hrep with h | h | h | h | h
  · exact .inl (ht ▸ h)
  · exact .inr (.inl (hv ▸ h))
  · exact .inr (.inr (.inl (hc ▸ h)))
  · exact .inr (.inr (.inr (.inl fun hl => h (ents_nil_of_log hro hl))))
  · exact .inr (.inr (.inr (.inr (hr ▸ h))))

/-- A `Ready` taken at a state with the view's term, vote, commit, log and role is not reported. -/
theorem not_reported {id : w64} {v : NodeView} {ps : PState} {rd : ReadyD}
    (hro : ReadyOutO N id v ps rd) (hrep : ReportedO v rd) (ht : ps.term = v.ps.term)
    (hv : ps.vote = v.ps.vote) (hc : ps.commit = v.ps.commit) (hl : ps.log = v.ps.log)
    (hr : ps.role = v.ps.role) : False := by
  rcases reported_changed hro hrep with h | h | h | h | h <;> contradiction

/-- **`Reach.stay` is never reported**: the `Ready` is at the view's own state. -/
theorem stay_quiet {id : w64} {v : NodeView} {rd : ReadyD} (hro : ReadyOutO N id v v.ps rd) :
    ¬ ReportedO v rd :=
  fun hrep => not_reported hro hrep rfl rfl rfl rfl rfl

/-! ## The kinds -/

/-- What the classification needs of a message delivered to the node (C4: a type in scope and
`MsgShape`). -/
def InMsg (m : Msg) : Prop :=
  (m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
    m.ty = .heartbeatResp ∨ m.ty = .propose) ∧
  (m.ty = .app → AppPayloadOk m) ∧ m.src ≠ m.dst ∧ (m.ty = .propose → m.term = W64 0)

/-! ## `Reach` read on the protocol state with the node flags off -/

/-- **`ReachP` with the node flags off** (stage A's reading; the `Ready` proofs are still over it):
no input; a received message stepped (`RecvEndO`), a tick (`TickEndO`), a proposal; `Advance`
stepping the queued self-messages (`AdvanceEndO`). -/
inductive ReachO (kk : NodeK) (c : CfgM) (id : w64) (net : List Msg) : NodeView → PState → Prop
  | stay (v : NodeView) : v.Idle → ReachO kk c id net v v.ps
  | recv (v : NodeView) (m : Msg) (ps₁ : PState) : v.Idle → v.byE = go!"recv" → v.cause = some m →
      m ∈ net → m.dst = id → m.term ≠ W64 0 → RecvEndO kk c id v.ps m ps₁ → ReachO kk c id net v ps₁
  | tick (v : NodeView) (ps₁ : PState) : v.Idle → TickBy v.byE → TickEndO kk c id v.ps ps₁ →
      ReachO kk c id net v ps₁
  | propose (v : NodeView) (d : List w8) (ps₁ : PState) : v.Idle → v.byE = go!"propose" →
      ProposeEnd c id v.ps (propMsg id d) ps₁ → ReachO kk c id net v ps₁
  | advance (v : NodeView) (ps₁ : PState) : v.pend = [] → v.ce = [] → DrainBy v.byE →
      AdvanceEndO kk c id v.ps v.qs ps₁ → ReachO kk c id net v ps₁

/-- With the node flags off and the S4 types only (`InMsg`), `ReachP` is `ReachO`: no new arm. -/
theorem ReachP.toO {c : CfgM} {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState}
    (hin : ∀ m ∈ net, InMsg m) (h : ReachP {} c id net v ps₁) : ReachO {} c id net v ps₁ := by
  cases h with
  | stay hi => exact .stay _ hi
  | recv m _ h1 h2 h3 h4 h5 h6 _ h7 => exact .recv _ m _ h1 h2 h3 h4 h5 h6 h7
  | recvP m _ _ _ _ hm _ _ _ hp =>
    exfalso
    have ht := (hin m hm).1
    rcases hp with ⟨-, h1 | h1, -⟩ | ⟨-, h1, -⟩ | ⟨⟨h1, -⟩, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    all_goals first
      | cases h1
      | (rcases ht with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] at h1 <;> cases h1)
  | tick _ h1 h2 h3 => exact .tick _ _ h1 h2 h3
  | tickP _ _ _ hp =>
    exfalso
    rcases hp with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> cases h1
  | propose d _ h1 h2 h3 => exact .propose _ d _ h1 h2 h3
  | advance _ h1 h2 h3 _ h4 => exact .advance _ _ h1 h2 h3 h4
  | advP _ _ _ _ _ _ hk _ => cases hk

/-- The message a drain caused by a `recv` handles (`Reach.input`'s): the drain's cause, sent to
the node, of a nonzero term. -/
def RecvAt (id : w64) (net : List Msg) (v : NodeView) (m : Msg) : Prop :=
  v.byE = go!"recv" ∧ v.cause = some m ∧ m ∈ net ∧ m.dst = id ∧ m.term ≠ W64 0

/-- The term and vote after a message handled by a non-leader (a `MsgApp`, a heartbeat): the
message's higher term adopted (the vote reset), or the node's own term, the node not a leader,
the vote kept. -/
def FolTerm (s : PState) (m : Msg) (ps₁ : PState) : Prop :=
  (uint.Z s.term < uint.Z m.term ∧ ps₁.vote = W64 0) ∨
  (m.term = s.term ∧ s.role ≠ .leader ∧ ps₁.vote = s.vote)

/-- A leader's commit index `c` at `s` (`maybeCommit`'s test): within its log, at an entry of its
term, its `Match` values at least `c` at a quorum of the three voters. -/
def CmtOk (cf : CfgM) (s : PState) (c : w64) : Prop :=
  uint.Z c ≤ plogLastIndexZ s.base s.log ∧ plogTermAt s.base s.log c = some s.term ∧
  JQuorum cf (ackedBy s c)

/-- A leader's steps from `y` to `s` that only raise its own `Match` (self-acknowledgements) and
possibly commit (`CmtOk`). -/
def LeadC (cf : CfgM) (id : w64) (y s : PState) : Prop :=
  s.role = .leader ∧ s.term = y.term ∧ s.vote = y.vote ∧ s.base = y.base ∧ s.log = y.log ∧
  (∀ j, j ≠ id → s.matched !! j = y.matched !! j) ∧
  (s.commit = y.commit ∨ (uint.Z y.commit < uint.Z s.commit ∧ CmtOk cf s s.commit))

/-- A follower's log after a `MsgApp` it accepts (`plogMaybeAppend`, from `base0`), with the
`Ready`'s entries: unchanged (every entry of the batch matches; no entries), or cut at the first
conflicting entry `e` (the batch's `d`-th, every one before it matching, at most one past the
log's end) and the batch from `e` on appended, which is the `Ready`'s entries (its first entry
`e`, at the cut `uint.nat e.Index' - 1`). -/
def StoreLog (s : PState) (m : Msg) (ps₁ : PState) (rd : ReadyD) : Prop :=
  (rd.ents = [] ∧ ps₁.log = s.log ∧
    ∀ (k : Nat) (e : EntryM), m.entries[k]? = some e → PlogMatches base0 s.log (entId e)) ∨
  (∃ (d : Nat) (e : EntryM), m.entries[d]? = some e ∧ rd.ents = m.entries.drop d ∧
    ¬ PlogMatches base0 s.log (entId e) ∧
    (∀ (k : Nat) (e' : EntryM), k < d → m.entries[k]? = some e' → PlogMatches base0 s.log (entId e')) ∧
    uint.Z e.Index' = uint.Z m.index + (d : Int) + 1 ∧ uint.Z e.Index' ≤ (s.log.length : Int) + 1 ∧
    ps₁.log = s.log.take (uint.nat e.Index' - 1) ++ rd.ents)

/-- No message in `s`'s outbox is addressed to the node itself: a leader's `Ready` that writes no
entry queues no self-acknowledgement (only `appendEntry` does, at a win or a proposal). -/
def NoSelf (id : w64) (s : PState) : Prop := ∀ q ∈ s.outbox, q.dst ≠ id

/-- **The kinds of a reported `Ready`** taken at `ps₁` from the view `v`, with the protocol facts
each kind's `OnDisk`/`InMemory` evaluation reads. -/
inductive ReadyKind (cf : CfgM) (id : w64) (net : List Msg) (v : NodeView) (ps₁ : PState) (rd : ReadyD) : Prop
  /-- `TickEndO`'s campaign (`elect`): the next term, the node's own vote, a candidate; nothing
  else written. -/
  | camp : TickBy v.byE → v.ps.role ≠ .leader → ps₁.term = v.ps.term + W64 1 →
      ps₁.vote = id → ps₁.role = .candidate → ps₁.log = v.ps.log → ps₁.commit = v.ps.commit →
      rd.ents = [] → ReadyKind cf id net v ps₁ rd
  /-- A vote granted to the request's sender at the request's term: a higher term adopted, or the
  node's own with no vote and no leader before; the request's log up to date. -/
  | grant (m : Msg) : RecvAt id net v m → m.ty = .vote →
      (uint.Z v.ps.term < uint.Z m.term ∨ (m.term = v.ps.term ∧ v.ps.vote = W64 0 ∧ v.ps.lead = W64 0)) →
      plogUpToDate v.ps.base v.ps.log (entryID.mk m.logterm m.index) = true →
      ps₁.term = m.term → ps₁.vote = m.src → ps₁.role = .follower → ps₁.log = v.ps.log →
      ps₁.commit = v.ps.commit → rd.ents = [] → ReadyKind cf id net v ps₁ rd
  /-- A term adopted only (`PreEndO`, the message's higher term): a follower with no vote. -/
  | adopt (m : Msg) : RecvAt id net v m → uint.Z v.ps.term < uint.Z m.term → ps₁.term = m.term →
      ps₁.vote = W64 0 → ps₁.role = .follower → ps₁.log = v.ps.log → ps₁.commit = v.ps.commit →
      rd.ents = [] → ReadyKind cf id net v ps₁ rd
  /-- A role change only: a candidate back to a follower at its term (a lost election, or a
  leader's message adopted, `padoptLeader`, with nothing stored or committed). -/
  | demote : v.ps.role = .candidate → ps₁.role = .follower → ps₁.term = v.ps.term →
      ps₁.vote = v.ps.vote → ps₁.log = v.ps.log → ps₁.commit = v.ps.commit → rd.ents = [] →
      ReadyKind cf id net v ps₁ rd
  /-- A follower's store and/or commit on a `MsgApp` it accepts (`AppEnd`'s accepting arm), maybe
  with the message's term adopted: the previous entry matched, the log as `StoreLog`, the commit
  kept or moved up to at most `min(m.commit, lastnewi)`. -/
  | store (m : Msg) : RecvAt id net v m → m.ty = .app → FolTerm v.ps m ps₁ → ps₁.term = m.term →
      ps₁.role = .follower → uint.Z v.ps.commit ≤ uint.Z m.index →
      PlogMatches base0 v.ps.log (entryID.mk m.logterm m.index) → StoreLog v.ps m ps₁ rd →
      (ps₁.commit = v.ps.commit ∨ (uint.Z v.ps.commit < uint.Z ps₁.commit ∧
        uint.Z ps₁.commit ≤ uint.Z m.commit ∧
        uint.Z ps₁.commit ≤ uint.Z m.index + (m.entries.length : Int))) →
      (ps₁.log ≠ v.ps.log ∨ ps₁.commit ≠ v.ps.commit) → ReadyKind cf id net v ps₁ rd
  /-- A follower's commit on a heartbeat, maybe with the message's term adopted: to `m.commit`. -/
  | hb (m : Msg) : RecvAt id net v m → m.ty = .heartbeat → FolTerm v.ps m ps₁ → ps₁.term = m.term →
      ps₁.role = .follower → ps₁.log = v.ps.log → uint.Z v.ps.commit < uint.Z ps₁.commit →
      ps₁.commit = m.commit → rd.ents = [] → ReadyKind cf id net v ps₁ rd
  /-- A candidate's win at its term (`WinEnd`), on a received vote response of its term or on its
  own vote (`Advance`): the tally with the vote recorded a quorum, the empty entry of its term
  appended (the `Ready`'s entry), the commit kept (a candidate's queued self-messages are all
  self-votes, which the new leader ignores). -/
  | win (src : w64) (rej : Bool) (mt : GMap w64 w64) : v.ps.role = .candidate →
      ((∃ m, RecvAt id net v m ∧ m.ty = .voteResp ∧ m.term = v.ps.term ∧ m.src = src ∧
          m.reject = rej) ∨
        (src = id ∧ rej = false ∧ ∃ q ∈ v.qs, q.ty = .voteResp)) →
      JQuorum cf (granted (recordVote v.ps.votes src (!rej))) →
      LeaderMatchOk id v.ps mt →
      LeadC cf id (pwinState id { v.ps with votes := recordVote v.ps.votes src (!rej) } mt) ps₁ →
      rd.ents = [pleaderEntry v.ps] → ps₁.commit = v.ps.commit → ReadyKind cf id net v ps₁ rd
  /-- A leader's proposal (`ProposeEnd`): entries stamped at its term appended at its end. -/
  | prop (es : List EntryM) : v.byE = go!"propose" → v.ps.role = .leader → es ≠ [] →
      rd.ents = es.mapIdx (stamp v.ps.term (plastIndex v.ps)) → ps₁.log = v.ps.log ++ rd.ents →
      ps₁.role = .leader → ps₁.term = v.ps.term → ps₁.vote = v.ps.vote → ps₁.commit = v.ps.commit →
      ReadyKind cf id net v ps₁ rd
  /-- A leader's commit (`cmt`: an acknowledgement, received or its own in `Advance`): the new
  commit `CmtOk` at the `Ready`'s state. -/
  | cmt : v.ps.role = .leader → ps₁.role = .leader → ps₁.term = v.ps.term → ps₁.vote = v.ps.vote →
      ps₁.log = v.ps.log → rd.ents = [] → uint.Z v.ps.commit < uint.Z ps₁.commit →
      CmtOk cf ps₁ ps₁.commit → NoSelf id ps₁ → ReadyKind cf id net v ps₁ rd

/-! ## Sets and tallies -/

theorem mem_ackedBy {s : PState} {c x : w64} :
    x ∈ ackedBy s c ↔ ∃ y, s.matched !! x = some y ∧ uint.Z c ≤ uint.Z y := by
  unfold ackedBy
  rw [GMap.elem_of_dom]
  simp only [GMap.lookup_filter]
  constructor
  · rintro ⟨y, hy⟩
    cases h : s.matched !! x with
    | none => rw [h] at hy; cases hy
    | some z =>
      rw [h] at hy
      refine ⟨z, rfl, ?_⟩
      by_cases hz : uint.Z c ≤ uint.Z z
      · exact hz
      · rw [Option.filter_some, if_neg (by simpa using hz)] at hy; cases hy
  · rintro ⟨y, hy, hle⟩
    exact ⟨y, by rw [hy, Option.filter_some, if_pos (by simpa using hle)]⟩

theorem jQuorum_mono {c : CfgM} {q q' : GSet w64} (h : JQuorum c q) (hs : ∀ x, x ∈ q → x ∈ q') :
    JQuorum c q' := by
  have hm : ∀ s : GSet w64, MajQ s q → MajQ s q' := by
    intro s hq
    rcases hq with h0 | hq
    · exact .inl h0
    · right
      unfold IsQuorum at hq ⊢
      have hsub : q ∩ s ⊆ q' ∩ s := by
        rw [GMap.elem_of_subseteq]; intro x hx
        rw [GMap.elem_of_intersection] at hx ⊢
        exact ⟨hs x hx.1, hx.2⟩
      have := GMap.subseteq_size hsub
      omega
  exact ⟨hm _ h.1, hm _ h.2⟩

/-- A `Match` raised (`MaybeUpdate`) keeps a commit's quorum. -/
theorem cmtOk_raise {s s' : PState} {c src x v' : w64} (h : CmtOk cf s c) (hb : s'.base = s.base)
    (hl : s'.log = s.log) (ht : s'.term = s.term) (hx : s.matched !! src = some x)
    (hxv : uint.Z x ≤ uint.Z v') (hm : s'.matched = <[src := v']> s.matched) : CmtOk cf s' c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hb, hl]; exact h1, by rw [hb, hl, ht]; exact h2, jQuorum_mono h3 fun w hw => ?_⟩
  obtain ⟨y, hy, hle⟩ := mem_ackedBy.mp hw
  refine mem_ackedBy.mpr ?_
  rw [hm]
  by_cases hws : w = src
  · subst hws; rw [hx] at hy; cases hy
    exact ⟨v', GMap.lookup_insert _ _ _, Int.le_trans hle hxv⟩
  · exact ⟨y, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hws)]; exact hy, hle⟩

theorem recordVote_idem (vs : GMap w64 Bool) (a : w64) (b : Bool) :
    recordVote (recordVote vs a b) a b = recordVote vs a b := by
  unfold recordVote
  cases h : vs !! a with
  | none => simp only [GMap.lookup_insert]
  | some _ => simp only [h]

theorem raise_ge (x i : w64) : uint.Z x ≤ uint.Z (if uint.Z x < uint.Z i then i else x) := by
  split <;> omega

/-! ## A received message -/

/-- What the preamble leaves (`PreEndO`): a higher term adopted (a follower with no vote), or the
node's own state. -/
def PreFacts (s : PState) (m : Msg) (s1 : PState) : Prop :=
  (uint.Z s.term < uint.Z m.term ∧ s1.vote = W64 0 ∧ s1.role = .follower) ∨ (m.term = s.term ∧ s1 = s)

/-- A received message's step that left the term, vote, log and commit as the preamble did, with
a follower (`padoptLeader`, or the preamble's): a term adopted, a candidate demoted, or nothing
reported. -/
theorem kind_of_adopt {id : w64} {net : List Msg} {v : NodeView} {s1 ps₁ : PState} {rd : ReadyD}
    {m : Msg} (hro : ReadyOutO N id v ps₁ rd) (hrep : ReportedO v rd) (hat : RecvAt id net v m)
    (ht1 : s1.term = m.term) (hl1 : s1.log = v.ps.log) (hc1 : s1.commit = v.ps.commit)
    (hpre : PreFacts v.ps m s1) (hnl : s1.role ≠ .leader)
    (ht : ps₁.term = s1.term) (hv : ps₁.vote = s1.vote) (hr : ps₁.role = .follower)
    (hl : ps₁.log = s1.log) (hc : ps₁.commit = s1.commit) : ReadyKind cf id net v ps₁ rd := by
  rcases hpre with ⟨hlt, hv0, -⟩ | ⟨hmt, rfl⟩
  · exact .adopt m hat hlt (ht.trans ht1) (hv.trans hv0) hr (hl.trans hl1) (hc.trans hc1)
      (ents_nil_of_log hro (hl.trans hl1))
  · cases hrole : v.ps.role with
    | follower => exact (not_reported hro hrep ht hv hc hl (hr.trans hrole.symm)).elim
    | candidate => exact .demote hrole hr ht hv hl hc (ents_nil_of_log hro hl)
    | leader => exact absurd hrole hnl

/-- A received message's step that left the preamble's state but for the outbox, tally, `Match`
or leader: a term adopted, or nothing reported. -/
theorem kind_of_s1 {id : w64} {net : List Msg} {v : NodeView} {s1 ps₁ : PState} {rd : ReadyD}
    {m : Msg} (hro : ReadyOutO N id v ps₁ rd) (hrep : ReportedO v rd) (hat : RecvAt id net v m)
    (ht1 : s1.term = m.term) (hl1 : s1.log = v.ps.log) (hc1 : s1.commit = v.ps.commit)
    (hpre : PreFacts v.ps m s1)
    (ht : ps₁.term = s1.term) (hv : ps₁.vote = s1.vote) (hr : ps₁.role = s1.role)
    (hl : ps₁.log = s1.log) (hc : ps₁.commit = s1.commit) : ReadyKind cf id net v ps₁ rd := by
  rcases hpre with ⟨hlt, hv0, hrf⟩ | ⟨hmt, rfl⟩
  · exact .adopt m hat hlt (ht.trans ht1) (hv.trans hv0) (hr.trans hrf) (hl.trans hl1)
      (hc.trans hc1) (ents_nil_of_log hro (hl.trans hl1))
  · exact (not_reported hro hrep ht hv hc hl hr).elim


/-- `commitTo(min(m.commit, lastnewi))`: the commit kept, or moved up to at most both. -/
theorem commitTo_min (c mc ln : w64) :
    plogCommitTo c (if uint.Z mc < uint.Z ln then mc else ln) = c ∨
    (uint.Z c < uint.Z (plogCommitTo c (if uint.Z mc < uint.Z ln then mc else ln)) ∧
      uint.Z (plogCommitTo c (if uint.Z mc < uint.Z ln then mc else ln)) ≤ uint.Z mc ∧
      uint.Z (plogCommitTo c (if uint.Z mc < uint.Z ln then mc else ln)) ≤ uint.Z ln) := by
  by_cases h1 : uint.Z mc < uint.Z ln
  · rw [if_pos h1]; unfold plogCommitTo; split
    · rename_i h2; exact .inr ⟨h2, Int.le_refl _, by omega⟩
    · exact .inl rfl
  · rw [if_neg h1]; unfold plogCommitTo; split
    · rename_i h2; exact .inr ⟨h2, by omega, Int.le_refl _⟩
    · exact .inl rfl

/-- **The type switch of a received message** (`HandleEndO`, at the state `s1` after the preamble),
reported: its kind. -/
theorem kind_handle {id : w64} {net : List Msg} {v : NodeView} {s1 ps₁ : PState} {rd : ReadyD}
    {m : Msg} (hro : ReadyOutO N id v ps₁ rd) (hrep : ReportedO v rd) (hb : v.ps.base = base0)
    (hid0 : id ≠ W64 0) (hvs : v.ps.role ≠ .follower → v.ps.vote = id)
    (hat : RecvAt id net v m) (hm : InMsg m)
    (ht1 : s1.term = m.term) (hl1 : s1.log = v.ps.log) (hc1 : s1.commit = v.ps.commit)
    (hb1 : s1.base = v.ps.base) (hpre : PreFacts v.ps m s1) (hX : s1.outbox = [])
    (h : HandleEndO kk cf id s1 m ps₁) : ReadyKind cf id net v ps₁ rd := by
  obtain ⟨hsc, hpay, -, hprop⟩ := hm
  have hm0 : m.term ≠ W64 0 := hat.2.2.2.2
  unfold HandleEndO at h
  rcases hsc with hty | hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · -- a vote request
    rcases h with ⟨hcv, hup, rfl⟩ | ⟨-, rfl⟩
    · rcases hpre with ⟨hlt, -, hrf⟩ | ⟨hmt, rfl⟩
      · exact .grant m hat hty (.inl hlt) (by rw [← hb1, ← hl1]; exact hup) ht1 rfl hrf hl1 hc1
          (ents_nil_of_log hro hl1)
      · by_cases hvm : v.ps.vote = m.src
        · exact (not_reported hro hrep rfl hvm.symm rfl rfl rfl).elim
        · have hv0 : v.ps.vote = W64 0 ∧ v.ps.lead = W64 0 := hcv.resolve_left hvm
          have hrf : v.ps.role = .follower := by
            by_cases hne : v.ps.role = .follower
            · exact hne
            · exact absurd ((hvs hne).symm.trans hv0.1) hid0
          exact .grant m hat hty (.inr ⟨hmt, hv0⟩) hup hmt.symm rfl hrf rfl rfl
            (ents_nil_of_log hro rfl)
    · exact kind_of_s1 hro hrep hat ht1 hl1 hc1 hpre rfl rfl rfl rfl rfl
  · -- a vote response
    split at h
    · rename_i hcand
      rcases hpre with ⟨-, -, hrf⟩ | ⟨hmt, rfl⟩
      · rw [hrf] at hcand; cases hcand
      · rcases h with ⟨-, rfl⟩ | ⟨hq, hw⟩ | ⟨-, rfl⟩
        · exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
        · obtain ⟨mt, ms, hlm, -, rfl⟩ := hw
          exact .win m.src m.reject mt hcand (.inl ⟨m, hat, hty, hmt, rfl, rfl⟩) hq hlm
            ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, .inl rfl⟩ (ents_of_append hro rfl) rfl
        · exact .demote hcand rfl rfl (by simp [pbecomeFollower]) rfl rfl (ents_nil_of_log hro rfl)
    · subst h; exact kind_of_s1 hro hrep hat ht1 hl1 hc1 hpre rfl rfl rfl rfl rfl
  · -- a `MsgApp`
    split at h
    · subst h; exact kind_of_s1 hro hrep hat ht1 hl1 hc1 hpre rfl rfl rfl rfl rfl
    · rename_i hnl
      rcases h with ⟨-, rfl⟩ | ⟨hle, lastnewi, es', hma, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩
      · exact kind_of_adopt hro hrep hat ht1 hl1 hc1 hpre hnl rfl rfl rfl rfl rfl
      · have hwf := hpay hty
        have hma' : plogMaybeAppend base0 v.ps.log (entryID.mk m.logterm m.index) m.entries =
            some (lastnewi, es') := by
          have h0 : plogMaybeAppend s1.base s1.log (entryID.mk m.logterm m.index) m.entries =
              some (lastnewi, es') := hma
          rw [hb1, hl1, hb] at h0; exact h0
        obtain ⟨hmatch, hlast, hcase⟩ := plogMaybeAppend_inv _ _ _ _ _ _ hwf.1 hwf.2 hma'
        simp only at hlast hcase
        by_cases hsame : es' = v.ps.log ∧
            plogCommitTo s1.commit (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi)
              = v.ps.commit
        · exact kind_of_adopt hro hrep hat ht1 hl1 hc1 hpre hnl rfl rfl rfl
            (hsame.1.trans hl1.symm) (hsame.2.trans hc1.symm)
        · refine .store m hat hty ?_ ht1 rfl (by rw [← hc1]; exact hle) hmatch ?_ ?_ ?_
          · rcases hpre with ⟨hlt, hv0, -⟩ | ⟨hmt, rfl⟩
            · exact .inl ⟨hlt, hv0⟩
            · exact .inr ⟨hmt, hnl, rfl⟩
          · rcases hcase with ⟨hes, hall⟩ | ⟨d, e, hd, hnm, hbef, hidx, hend, hes⟩
            · exact .inl ⟨ents_nil_of_log hro hes, hes, hall⟩
            · have hb0 : uint.Z base0.index' = 0 := by simp [base0]
              have hend' : uint.Z e.Index' ≤ (v.ps.log.length : Int) + 1 := by
                unfold plogLastIndexZ at hend; rw [hb0] at hend; omega
              have := uint_Z_nonneg m.index
              have hnat : ((uint.nat e.Index' : Nat) : Int) = uint.Z e.Index' := by word
              have hk : (uint.Z e.Index' - uint.Z base0.index' - 1).toNat = uint.nat e.Index' - 1 := by
                rw [hb0]; omega
              rw [hk] at hes
              have hdrop := list_drop_S m.entries d e hd
              have hY : v.ps.log[uint.nat e.Index' - 1]? ≠ some e := by
                intro hx; apply hnm
                exact plogTermAt_lookup base0 v.ps.log e.Index' _ e hx (by rw [hb0]; omega)
              have hents := ents_of_split hro (k := uint.nat e.Index' - 1) (by omega)
                (by rw [hdrop] at hes; exact hes) hY
              rw [← hdrop] at hents
              exact .inr ⟨d, e, hd, hents, hnm, hbef, hidx, hend', by rw [hents]; exact hes⟩
          · rcases commitTo_min s1.commit m.commit lastnewi with h | ⟨h1, h2, h3⟩
            · exact .inl (h.trans hc1)
            · exact .inr ⟨by rw [← hc1]; exact h1, h2, by rw [← hlast]; exact h3⟩
          · by_cases h1 : es' = v.ps.log
            · exact .inr fun h2 => hsame ⟨h1, h2⟩
            · exact .inl h1
      · exact kind_of_adopt hro hrep hat ht1 hl1 hc1 hpre hnl rfl rfl rfl rfl rfl
  · -- a `MsgAppResp`
    split at h
    · rename_i hlead
      rcases hpre with ⟨-, -, hrf⟩ | ⟨hmt, rfl⟩
      · rw [hrf] at hlead; cases hlead
      · unfold AppRespEndO at h
        rcases h with ⟨-, rfl⟩ | ⟨-, -, ms, -, rfl⟩ | ⟨-, x, n, -, hn, ms, hms, rfl⟩
        · exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
        · exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
        · rcases hn with rfl | hpc
          · exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
          · exact .cmt hlead hlead rfl rfl rfl (ents_nil_of_log hro rfl) hpc.1
              ⟨hpc.2.1, hpc.2.2.1, hpc.2.2.2⟩
              (fun q hq => (hms q (mem_psend (X := { v.ps with matched := _, commit := n }) hX hq)).1.2.2.2.1)
    · subst h; exact kind_of_s1 hro hrep hat ht1 hl1 hc1 hpre rfl rfl rfl rfl rfl
  · -- a heartbeat
    split at h
    · subst h; exact kind_of_s1 hro hrep hat ht1 hl1 hc1 hpre rfl rfl rfl rfl rfl
    · rename_i hnl
      subst h
      by_cases hcm : plogCommitTo s1.commit m.commit = s1.commit
      · exact kind_of_adopt hro hrep hat ht1 hl1 hc1 hpre hnl rfl rfl rfl rfl hcm
      · have hlt : uint.Z s1.commit < uint.Z m.commit := by
          unfold plogCommitTo at hcm
          split at hcm
          · assumption
          · exact absurd rfl hcm
        have hcv : plogCommitTo s1.commit m.commit = m.commit := by
          unfold plogCommitTo; rw [if_pos hlt]
        have h2 : uint.Z v.ps.commit < uint.Z (plogCommitTo s1.commit m.commit) := by
          rw [hcv, ← hc1]; exact hlt
        refine .hb m hat hty ?_ ht1 rfl hl1 h2 hcv (ents_nil_of_log hro hl1)
        rcases hpre with ⟨hlt', hv0, -⟩ | ⟨hmt, rfl⟩
        · exact .inl ⟨hlt', hv0⟩
        · exact .inr ⟨hmt, hnl, rfl⟩
  · -- a heartbeat response
    split at h
    · rename_i hlead
      rcases hpre with ⟨-, -, hrf⟩ | ⟨hmt, rfl⟩
      · rw [hrf] at hlead; cases hlead
      · obtain ⟨ms, -, rfl⟩ := h; exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
    · subst h; exact kind_of_s1 hro hrep hat ht1 hl1 hc1 hpre rfl rfl rfl rfl rfl
  · exact absurd (hprop hty) hm0

/-- **A received message's step** (`RecvEndO`, its term not `0`), reported: its kind. -/
theorem kind_recv {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {rd : ReadyD}
    {m : Msg} (hro : ReadyOutO N id v ps₁ rd) (hrep : ReportedO v rd) (hb : v.ps.base = base0)
    (hid0 : id ≠ W64 0) (hvs : v.ps.role ≠ .follower → v.ps.vote = id)
    (hat : RecvAt id net v m) (hm : InMsg m) (h : RecvEndO kk cf id v.ps m ps₁) (hX : v.ps.outbox = []) :
    ReadyKind cf id net v ps₁ rd := by
  rcases h with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
  · exact absurd h0 hat.2.2.2.2
  · exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
  · rcases hpre with ⟨hlt, rfl⟩ | ⟨hmt, rfl⟩
    · have hne : m.term ≠ v.ps.term := fun h => by rw [h] at hlt; exact Int.lt_irrefl _ hlt
      exact kind_handle (s1 := pbecomeFollower v.ps m.term _) hro hrep hb hid0 hvs hat hm rfl rfl
        rfl rfl (.inl ⟨hlt, by simp [pbecomeFollower, hne], rfl⟩) hX hh
    · exact kind_handle (s1 := v.ps) hro hrep hb hid0 hvs hat hm hmt.symm rfl rfl rfl
        (.inr ⟨hmt, rfl⟩) hX hh


/-! ## A tick, a proposal -/

/-- **A tick's step** (`TickEndO`), reported: a campaign (nothing, or a leader's heartbeats, change
nothing reported). -/
theorem kind_tick {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {rd : ReadyD}
    (hro : ReadyOutO N id v ps₁ rd) (hrep : ReportedO v rd) (hby : TickBy v.byE)
    (h : TickEndO kk cf id v.ps ps₁) : ReadyKind cf id net v ps₁ rd := by
  rcases h with rfl | ⟨hnl, -, peers, cl, -, rfl⟩ | ⟨-, ms, -, rfl⟩
  · exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
  · exact .camp hby hnl rfl rfl rfl rfl rfl (ents_nil_of_log hro rfl)
  · exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim

/-- **A proposal's step** (`ProposeEnd` of `RawNode.Propose`'s message), reported: a leader's
append (a drop, a forward change nothing reported). -/
theorem kind_propose {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {rd : ReadyD}
    {d : List w8} (hro : ReadyOutO N id v ps₁ rd) (hrep : ReportedO v rd)
    (hby : v.byE = go!"propose") (h : ProposeEnd cf id v.ps (propMsg id d) ps₁) :
    ReadyKind cf id net v ps₁ rd := by
  unfold ProposeEnd at h
  split at h
  · rename_i hlead
    rcases h with rfl | ⟨es, ms, hpr, -, rfl⟩
    · exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
    · have hne : es ≠ [] := by
        intro h0; have := hpr.length; rw [h0] at this; simp [propMsg] at this
      have hents := ents_of_append hro (es := es.mapIdx (stamp v.ps.term (plastIndex v.ps))) rfl
      exact .prop es hby hlead hne hents (by rw [hents]; rfl) hlead rfl rfl rfl
  · split at h
    · subst h; exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
    · subst h; exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim

/-! ## `Advance` -/

/-- The phases of `Advance`'s run from `s₀` (`W`: a self-vote was stepped): unchanged but for a
candidate's own vote tallied; a leader's self-acknowledgements (`LeadC`); a candidate lost
(a follower, nothing else changed); a candidate won on its own vote, then (its queued messages all
self-votes) nothing that changes the commit. -/
def AdvP (cf : CfgM) (id : w64) (s₀ : PState) (W : Prop) (s : PState) : Prop :=
  (s = s₀ ∨ (s₀.role = .candidate ∧ s = { s₀ with votes := recordVote s₀.votes id true })) ∨
  (s₀.role = .leader ∧ LeadC cf id s₀ s ∧ NoSelf id s) ∨
  (s₀.role = .candidate ∧ s.role = .follower ∧ s.term = s₀.term ∧ s.vote = s₀.vote ∧
    s.log = s₀.log ∧ s.commit = s₀.commit) ∨
  (s₀.role = .candidate ∧ W ∧ ∃ mt, JQuorum cf (granted (recordVote s₀.votes id true)) ∧
    LeaderMatchOk id s₀ mt ∧
    LeadC cf id (pwinState id { s₀ with votes := recordVote s₀.votes id true } mt) s ∧
    s.commit = s₀.commit)

theorem AdvP.term {id : w64} {s₀ s : PState} {W : Prop} (h : AdvP cf id s₀ W s) : s.term = s₀.term := by
  rcases h with (heq | ⟨-, heq⟩) | ⟨-, hl, -⟩ | ⟨-, -, ht, -⟩ | ⟨-, -, mt, -, -, hl, -⟩
  · rw [heq]
  · rw [heq]
  · exact hl.2.1
  · exact ht
  · exact hl.2.1

theorem leadC_refl {id : w64} {s : PState} (h : s.role = .leader) : LeadC cf id s s :=
  ⟨h, rfl, rfl, rfl, rfl, fun _ _ => rfl, .inl rfl⟩

/-- A self-addressed message's type switch at a leader keeps `LeadC`: a self-acknowledgement
raises only its own `Match` and commits only by `PCommitOk`; a vote response is ignored. -/
theorem leadC_step {id : w64} {y s s' : PState} {q : Msg} (hL : LeadC cf id y s) (hqs : q.src = id)
    (hrj : q.reject = false) (hty : q.ty = .appResp ∨ q.ty = .voteResp)
    (h : HandleEndO kk cf id s q s') : LeadC cf id y s' := by
  obtain ⟨hr, ht, hv, hb, hl, hm, hc⟩ := hL
  unfold HandleEndO at h
  rcases hty with hty | hty <;> rw [hty] at h <;> simp only at h
  · rw [if_pos hr] at h
    unfold AppRespEndO at h
    rcases h with ⟨-, rfl⟩ | ⟨h', -⟩ | ⟨-, x, n, hx, hn, ms, -, rfl⟩
    · exact ⟨hr, ht, hv, hb, hl, hm, hc⟩
    · rw [hrj] at h'; cases h'
    · have hyc : uint.Z y.commit ≤ uint.Z s.commit := by
        rcases hc with hc | hc
        · rw [hc]; exact Int.le_refl _
        · exact Int.le_of_lt hc.1
      refine ⟨hr, ht, hv, hb, hl, fun j hj => ?_, ?_⟩
      · show (<[q.src := _]> s.matched) !! j = _
        rw [hqs, GMap.lookup_insert_ne _ _ (fun h => hj h.symm)]; exact hm j hj
      · rcases hn with rfl | hpc
        · rcases hc with hc | ⟨hlt, hcm⟩
          · exact .inl hc
          · exact .inr ⟨hlt, cmtOk_raise hcm rfl rfl rfl hx (raise_ge x q.index) rfl⟩
        · exact .inr ⟨Int.lt_of_le_of_lt hyc hpc.1, hpc.2.1, hpc.2.2.1, hpc.2.2.2⟩
  · rw [if_neg (by rw [hr]; decide)] at h
    subst h; exact ⟨hr, ht, hv, hb, hl, hm, hc⟩

/-- A leader's step of a self-addressed message queues nothing to itself. -/
theorem noSelf_step {id : w64} {s s' : PState} {q : Msg} (hr : s.role = .leader) (hn : NoSelf id s)
    (hrj : q.reject = false) (hty : q.ty = .appResp ∨ q.ty = .voteResp)
    (h : HandleEndO kk cf id s q s') : NoSelf id s' := by
  unfold HandleEndO at h
  rcases hty with hty | hty <;> rw [hty] at h <;> simp only at h
  · rw [if_pos hr] at h
    unfold AppRespEndO at h
    rcases h with ⟨-, rfl⟩ | ⟨h', -⟩ | ⟨-, x, c, -, -, ms, hms, rfl⟩
    · exact hn
    · rw [hrj] at h'; cases h'
    · intro y hy
      rw [psendMsgs_outbox] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hn y hy
      · exact (hms y hy).1.2.2.2.1
  · rw [if_neg (by rw [hr]; decide)] at h
    subst h; exact hn

/-- One step of `Advance` keeps `AdvP`. -/
theorem advP_step {id : w64} {s₀ s s' : PState} {W : Prop} {q : Msg} (hi : AdvP cf id s₀ W s)
    (hX0 : s₀.outbox = []) (hq : SelfMsg id s₀.term q) (hW : q.ty = .voteResp → W)
    (hC : s₀.role = .candidate → q.ty = .voteResp) (h : RecvEndO kk cf id s q s') :
    AdvP cf id s₀ W s' := by
  obtain ⟨hqs, -, hqt, hrj, hty⟩ := hq
  have hqt' : q.term = s.term := hqt.trans hi.term.symm
  have hh : HandleEndO kk cf id s q s' := by
    rcases h with ⟨-, hh⟩ | ⟨-, hlt, -⟩ | ⟨-, s2, hpre, hh⟩
    · exact hh
    · rw [hqt'] at hlt; exact absurd hlt (Int.lt_irrefl _)
    · rcases hpre with ⟨hlt, -⟩ | ⟨-, rfl⟩
      · rw [hqt'] at hlt; exact absurd hlt (Int.lt_irrefl _)
      · exact hh
  have hlead : ∀ y, LeadC cf id y s → LeadC cf id y s' := fun y hL => leadC_step hL hqs hrj hty hh
  have hns : s.role = .leader → NoSelf id s → NoSelf id s' := fun hr hn => noSelf_step hr hn hrj hty hh
  rcases hi with (heq | ⟨hc, heq⟩) | ⟨hl0, hL, hn0⟩ | ⟨hc, hf, ht, hv, hl, hcm⟩ |
      ⟨hc, hw, mt, hq, hlm, hL, hcm⟩
  · rw [heq] at hh hlead hns
    by_cases hl0 : s₀.role = .leader
    · exact .inr (.inl ⟨hl0, hlead _ (leadC_refl hl0), hns hl0 (fun x hx => by rw [hX0] at hx; cases hx)⟩)
    · unfold HandleEndO at hh
      rcases hty with hty | hty <;> rw [hty] at hh <;> simp only at hh
      · rw [if_neg hl0] at hh; subst hh; exact .inl (.inl rfl)
      · split at hh
        · rename_i hc
          rw [hqs, hrj] at hh
          rcases hh with ⟨-, rfl⟩ | ⟨hq, hw⟩ | ⟨-, rfl⟩
          · exact .inl (.inr ⟨hc, rfl⟩)
          · obtain ⟨mt, ms, hlm, -, rfl⟩ := hw
            exact .inr (.inr (.inr ⟨hc, hW hty, mt, hq, hlm,
              ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, .inl rfl⟩, rfl⟩))
          · exact .inr (.inr (.inl ⟨hc, rfl, rfl, by simp [pbecomeFollower], rfl, rfl⟩))
        · subst hh; exact .inl (.inl rfl)
  · rw [heq] at hh
    unfold HandleEndO at hh
    rcases hty with hty | hty <;> rw [hty] at hh <;> simp only at hh
    · rw [if_neg (by rw [hc]; decide)] at hh; subst hh; exact .inl (.inr ⟨hc, rfl⟩)
    · rw [if_pos hc] at hh
      rw [hqs, hrj] at hh
      have hid : recordVote (recordVote s₀.votes id true) id (!false) = recordVote s₀.votes id true :=
        recordVote_idem _ _ _
      rw [hid] at hh
      rcases hh with ⟨-, rfl⟩ | ⟨hq, hw⟩ | ⟨-, rfl⟩
      · exact .inl (.inr ⟨hc, rfl⟩)
      · obtain ⟨mt, ms, hlm, -, rfl⟩ := hw
        exact .inr (.inr (.inr ⟨hc, hW hty, mt, hq, hlm,
          ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, .inl rfl⟩, rfl⟩))
      · exact .inr (.inr (.inl ⟨hc, rfl, rfl, by simp [pbecomeFollower], rfl, rfl⟩))
  · exact .inr (.inl ⟨hl0, hlead _ hL, hns hL.1 hn0⟩)
  · unfold HandleEndO at hh
    rcases hty with hty | hty <;> rw [hty] at hh <;> simp only at hh
    · rw [if_neg (by rw [hf]; decide)] at hh; subst hh
      exact .inr (.inr (.inl ⟨hc, hf, ht, hv, hl, hcm⟩))
    · rw [if_neg (by rw [hf]; decide)] at hh; subst hh
      exact .inr (.inr (.inl ⟨hc, hf, ht, hv, hl, hcm⟩))
  · -- won: the message is a self-vote (`hC`), which a leader ignores
    have hv : q.ty = .voteResp := hC hc
    unfold HandleEndO at hh
    rw [hv] at hh; simp only at hh
    rw [if_neg (by rw [hL.1]; decide)] at hh; subst hh
    exact .inr (.inr (.inr ⟨hc, hw, mt, hq, hlm, hL, hcm⟩))

theorem advP_run {id : w64} {s₀ s s' : PState} {qs : List Msg} {W : Prop}
    (hX0 : s₀.outbox = []) (h : AdvanceEndO kk cf id s qs s') (hq : ∀ q ∈ qs, SelfMsg id s₀.term q)
    (hW : ∀ q ∈ qs, q.ty = .voteResp → W) (hC : ∀ q ∈ qs, s₀.role = .candidate → q.ty = .voteResp)
    (hi : AdvP cf id s₀ W s) : AdvP cf id s₀ W s' := by
  induction h with
  | nil => exact hi
  | cons s s1 s' q qs hr _ ih =>
    exact ih (fun x hx => hq x (List.mem_cons_of_mem _ hx))
      (fun x hx => hW x (List.mem_cons_of_mem _ hx)) (fun x hx => hC x (List.mem_cons_of_mem _ hx))
      (advP_step hi hX0 (hq q (List.mem_cons_self ..)) (hW q (List.mem_cons_self ..))
        (hC q (List.mem_cons_self ..)) hr)

/-- **`Advance`'s run** (a drain's later `Ready`), reported: a leader's commit, a candidate's loss,
or its win on its own vote; never a term or vote change. -/
theorem kind_advance {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {rd : ReadyD}
    (hro : ReadyOutO N id v ps₁ rd) (hrep : ReportedO v rd)
    (hqs : ∀ q ∈ v.qs, SelfMsg id v.ps.term q)
    (hqc : v.ps.role = .candidate → ∀ q ∈ v.qs, q.ty = .voteResp)
    (h : AdvanceEndO kk cf id v.ps v.qs ps₁) (hX : v.ps.outbox = []) :
    ReadyKind cf id net v ps₁ rd := by
  have hP : AdvP cf id v.ps (∃ q ∈ v.qs, q.ty = .voteResp) ps₁ :=
    advP_run hX h hqs (fun q hq hty => ⟨q, hq, hty⟩) (fun q hq hc => hqc hc q hq) (.inl (.inl rfl))
  rcases hP with (heq | ⟨-, heq⟩) | ⟨hl0, hL, hns⟩ | ⟨hc, hf, ht, hv, hl, hcm⟩ |
      ⟨hc, hw, mt, hq, hlm, hL, hpc⟩
  · subst heq; exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
  · subst heq; exact (not_reported hro hrep rfl rfl rfl rfl rfl).elim
  · obtain ⟨hr, ht, hv, -, hl, -, hc⟩ := hL
    rcases hc with hc | ⟨hlt, hcm⟩
    · exact (not_reported hro hrep ht hv hc hl (hr.trans hl0.symm)).elim
    · exact .cmt hl0 hr ht hv hl (ents_nil_of_log hro hl) hlt hcm hns
  · exact .demote hc hf ht hv hl hcm (ents_nil_of_log hro hl)
  · exact .win id false mt hc (.inr ⟨rfl, rfl, hw⟩) hq hlm hL
      (ents_of_append hro (es := [pleaderEntry v.ps]) hL.2.2.2.2.1) hpc

/-! ## The classification -/

/-- **The kind of a reported `Ready`** (`antSim_ready`'s raft side): from the view `v` (its base
`base0`, a non-follower's vote its own, its queued self-messages at its term), the node `id ≠ 0`
reaching `ps₁` (`Reach`; the messages sent of a type in scope and `MsgShape`), a `Ready` at `ps₁`
(`ReadyOutP`) that the harness reports (`Reported`) is one of `ReadyKind`'s. -/
theorem ready_kind {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {rd : ReadyD}
    (hr : ReachO kk cf id net v ps₁) (hro : ReadyOutO N id v ps₁ rd) (hrep : ReportedO v rd)
    (hb : v.ps.base = base0) (hid0 : id ≠ W64 0) (hvs : v.ps.role ≠ .follower → v.ps.vote = id)
    (hin : ∀ m ∈ net, InMsg m) (hqs : ∀ q ∈ v.qs, SelfMsg id v.ps.term q)
    (hqc : v.ps.role = .candidate → ∀ q ∈ v.qs, q.ty = .voteResp) (hX : v.ps.outbox = []) :
    ReadyKind cf id net v ps₁ rd := by
  cases hr with
  | stay _ => exact absurd hrep (stay_quiet hro)
  | recv m _ _ hbe hca hmn hmd hm0 hs =>
    exact kind_recv hro hrep hb hid0 hvs ⟨hbe, hca, hmn, hmd, hm0⟩ (hin m hmn) hs hX
  | tick _ _ hbe hs => exact kind_tick hro hrep hbe hs
  | propose d _ _ hbe hs => exact kind_propose hro hrep hbe hs
  | advance _ _ _ _ ha => exact kind_advance hro hrep hqs hqc ha hX


/-! ## A non-follower's vote is its own -/

/-- A reported `Ready`'s state keeps "a non-follower's vote is its own" (`GhostState`'s
`s.role ≠ .follower → s.vote = id`): a campaign votes for itself, a win and a leader's steps keep
the vote, the other kinds are followers'. -/
theorem voteSelf_kind {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {rd : ReadyD}
    (hk : ReadyKind cf id net v ps₁ rd) (hvs : v.ps.role ≠ .follower → v.ps.vote = id) :
    ps₁.role ≠ .follower → ps₁.vote = id := by
  intro hne
  cases hk with
  | camp _ _ _ hv => exact hv
  | grant m _ _ _ _ _ _ hr => exact absurd hr hne
  | adopt m _ _ _ _ hr => exact absurd hr hne
  | demote _ hr => exact absurd hr hne
  | store m _ _ _ _ hr => exact absurd hr hne
  | hb m _ _ _ _ hr => exact absurd hr hne
  | win src rej mt hc _ _ _ hL => rw [hL.2.2.1]; exact hvs (by rw [hc]; decide)
  | prop es _ hl _ _ _ _ _ hv => rw [hv]; exact hvs (by rw [hl]; decide)
  | cmt hl _ _ hv => rw [hv]; exact hvs (by rw [hl]; decide)

/-- Any `Ready` (reported or not) keeps it. -/
theorem voteSelf_ready {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState} {rd : ReadyD}
    (hr : ReachO kk cf id net v ps₁) (hro : ReadyOutO N id v ps₁ rd)
    (hb : v.ps.base = base0) (hid0 : id ≠ W64 0) (hvs : v.ps.role ≠ .follower → v.ps.vote = id)
    (hin : ∀ m ∈ net, InMsg m) (hqs : ∀ q ∈ v.qs, SelfMsg id v.ps.term q)
    (hqc : v.ps.role = .candidate → ∀ q ∈ v.qs, q.ty = .voteResp) (hX : v.ps.outbox = []) :
    ps₁.role ≠ .follower → ps₁.vote = id := by
  by_cases hrep : ReportedO v rd
  · exact voteSelf_kind (ready_kind hr hro hrep hb hid0 hvs hin hqs hqc hX) hvs
  · have hrr : rd.role = v.ps.role := by
      by_cases h : rd.role = v.ps.role
      · exact h
      · exact absurd (.inr (.inr (.inr (.inr h)))) hrep
    have hvv : rd.vote = v.ps.vote := by
      by_cases h : rd.vote = v.ps.vote
      · exact h
      · exact absurd (.inr (.inl h)) hrep
    rw [← hro.1, hrr, ← hro.2.2.1, hvv]; exact hvs

/-! ## The outbox's self-addressed messages -/

/-- **The self-addressed messages in `s`'s outbox** (`stepsOnAdvance`'s): a leader's
self-acknowledgement of its log (`pselfAck`: at its term and last index, `reject = false`), or a
candidate's self-vote (at its term, `reject = false`). -/
def SelfOut (id : w64) (s : PState) : Prop :=
  ∀ q ∈ s.outbox, q.dst = id →
    (s.role = .leader ∧ q = pselfAck id s) ∨
    (s.role = .candidate ∧ q = Msg.plain .voteResp id id s.term false)

theorem selfOut_nil {id : w64} {s : PState} (h : s.outbox = []) : SelfOut id s :=
  fun q hq => by rw [h] at hq; cases hq

theorem selfOut_none {id : w64} {X : PState} {ms : List Msg} (hX : X.outbox = [])
    (h : ∀ x ∈ ms, x.dst ≠ id) : SelfOut id (psendMsgs X ms) :=
  fun q hq hd => absurd hd (h q (mem_psend hX hq))

theorem selfOut_one {id : w64} {X : PState} {x : Msg} (hX : X.outbox = []) (h : x.dst ≠ id) :
    SelfOut id (psendMsgs X [x]) :=
  selfOut_none hX fun y hy => by rw [List.mem_singleton.mp hy]; exact h

theorem selfOut_ack {id : w64} {X : PState} {ms : List Msg} (hX : X.outbox = [])
    (hr : X.role = .leader) (h : ∀ x ∈ ms, x.dst ≠ id) :
    SelfOut id (psendMsgs X ([pselfAck id X] ++ ms)) := by
  intro q hq hd
  rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
  · rw [List.mem_singleton] at hq; exact .inl ⟨hr, hq⟩
  · exact absurd hd (h q hq)

theorem selfOut_sends {id : w64} {X s' : PState} (hX : X.outbox = []) (h : SendsEnd cf id X s') :
    SelfOut id s' := by
  obtain ⟨ms, hms, rfl⟩ := h
  exact selfOut_none hX fun x hx => (hms x hx).1.2.2.2.1

/-- The type switch's messages (at the state after the preamble, nothing queued) for a received
message from another node: answers to its sender, a leader's `MsgApp`s, a win's
self-acknowledgement. -/
theorem selfOut_handle {id : w64} {s1 s' : PState} {m : Msg} (hX : s1.outbox = [])
    (hne : m.src ≠ id)
    (hsc : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨ m.ty = .heartbeat ∨
      m.ty = .heartbeatResp)
    (h : HandleEndO kk cf id s1 m s') : SelfOut id s' := by
  unfold HandleEndO at h
  rcases hsc with hty | hty | hty | hty | hty | hty <;> rw [hty] at h <;> simp only at h
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact selfOut_one (X := { s1 with vote := m.src }) hX hne
    · exact selfOut_one hX hne
  · split at h
    · rcases h with ⟨-, rfl⟩ | ⟨-, mt, ms, -, hms, rfl⟩ | ⟨-, rfl⟩
      · exact selfOut_nil hX
      · exact selfOut_ack hX rfl fun x hx => (hms x hx).1.2.2.2.1
      · exact selfOut_nil hX
    · subst h; exact selfOut_nil hX
  · split at h
    · subst h; exact selfOut_nil hX
    · rcases h with ⟨-, rfl⟩ | ⟨-, _, _, -, rfl⟩ | ⟨-, -, hint, hintterm, -, -, rfl⟩
      · exact selfOut_one (X := padoptLeader s1 m.src) hX hne
      · exact selfOut_one hX hne
      · exact selfOut_one (X := padoptLeader s1 m.src) hX hne
  · split at h
    · unfold AppRespEndO at h
      rcases h with ⟨-, rfl⟩ | ⟨-, -, hs⟩ | ⟨-, x, n, -, -, hs⟩
      · exact selfOut_nil hX
      · exact selfOut_sends hX hs
      · exact selfOut_sends (X := { s1 with matched := _, commit := n }) hX hs
    · subst h; exact selfOut_nil hX
  · split at h
    · subst h; exact selfOut_nil hX
    · subst h; exact selfOut_one hX hne
  · split at h
    · exact selfOut_sends hX h
    · subst h; exact selfOut_nil hX

/-- **The self-addressed messages at a `Ready`'s state** (`Reach`): a leader's
self-acknowledgement or a candidate's self-vote. From the view (nothing queued, C1; the leader
hint `LeadOk`; its queued self-messages at its term) and the messages sent (`InMsg`). -/
theorem selfOut_reach {id : w64} {net : List Msg} {v : NodeView} {ps₁ : PState}
    (hr : ReachO kk cf id net v ps₁) (hX : v.ps.outbox = [])
    (hlo : v.ps.role ≠ .leader → v.ps.lead ≠ id) (hin : ∀ m ∈ net, InMsg m)
    (hqs : ∀ q ∈ v.qs, SelfMsg id v.ps.term q) : SelfOut id ps₁ := by
  cases hr with
  | stay _ => exact selfOut_nil hX
  | recv m _ _ _ _ hmn hmd hm0 hs =>
    obtain ⟨hsc, -, hsd, hprop⟩ := hin m hmn
    have hne : m.src ≠ id := hmd ▸ hsd
    have hsc' : m.ty = .vote ∨ m.ty = .voteResp ∨ m.ty = .app ∨ m.ty = .appResp ∨
        m.ty = .heartbeat ∨ m.ty = .heartbeatResp := by
      rcases hsc with h | h | h | h | h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr (.inl h))))
      · exact .inr (.inr (.inr (.inr (.inr h))))
      · exact absurd (hprop h) hm0
    rcases hs with ⟨h0, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s1, hpre, hh⟩
    · exact absurd h0 hm0
    · exact selfOut_nil hX
    · exact selfOut_handle ((preEnd_facts hpre).1.trans hX) hne hsc' hh
  | tick _ _ _ hs =>
    rcases hs with rfl | ⟨-, hid, peers, cl, hperm, rfl⟩ | ⟨-, ms, hms, rfl⟩
    · exact selfOut_nil hX
    · intro q hq hd
      rcases List.mem_append.mp (mem_psend hX hq) with hq | hq
      · rw [List.mem_singleton] at hq; exact .inr ⟨rfl, hq⟩
      · obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hq
        exfalso
        have h1 := (GMap.elem_of_elements _ _).mp (hperm.mem_iff.mp hd')
        rw [GMap.elem_of_difference, GMap.elem_of_singleton] at h1
        exact h1.2 hd
    · exact selfOut_none hX fun x hx => (hms x hx).1.2.2.2.1
  | propose d _ _ _ hs =>
    have hs' : ProposeEnd cf id v.ps (propMsg id d) ps₁ := hs
    unfold ProposeEnd at hs'
    split at hs'
    · rename_i hlead
      rcases hs' with rfl | ⟨es, ms, -, hms, rfl⟩
      · exact selfOut_nil hX
      · exact selfOut_ack (X := pappend v.ps _) hX hlead fun x hx => (hms x hx).1.2.2.2.1
    · rename_i hnl
      split at hs'
      · rename_i hf
        subst hs'
        exact selfOut_one hX (hlo hnl)
      · subst hs'; exact selfOut_nil hX
  | advance _ _ _ _ ha =>
    have hinv : AdvInv id v.ps.term v.ps.commit ps₁ :=
      adv_run ha hqs (advInv_nil rfl (Int.le_refl _) hX)
    intro q hq hd
    obtain ⟨hr, -, hself⟩ := hinv.2.2 q hq
    exact .inl ⟨hr, hself hd⟩

/-- **A `Ready`'s queued self-messages** (`ReadyOutP`'s `qs`): `SelfMsg`s at its term, each a
leader's self-acknowledgement or a candidate's self-vote (what `QsOk` reads). -/
theorem qs_self {id : w64} {v : NodeView} {ps : PState} {rd : ReadyD}
    (hro : ReadyOutO N id v ps rd) (hso : SelfOut id ps) :
    ∀ q ∈ rd.qs, SelfMsg id ps.term q ∧
      ((ps.role = .leader ∧ q = pselfAck id ps) ∨
        (ps.role = .candidate ∧ q = Msg.plain .voteResp id id ps.term false)) := by
  intro q hq
  have hq' := (hro.2.2.2.2.2.2.1.mem_iff).mp hq
  rw [List.mem_filter] at hq'
  have hd : q.dst = id := of_decide_eq_true hq'.2
  have hk := hso q hq'.1 hd
  refine ⟨?_, hk⟩
  rcases hk with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, .inl rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, .inr rfl⟩


end kind

end AntSim
end EtcdGrove
end Perennial
