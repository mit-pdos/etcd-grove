/-
Port of `election_proof/inv_tracker.v` (at feb5c73d4): the progress tracker and per-peer
progress.

Since 2026-09-16 these are **definitions, not axioms**. The tracker is core raft, so it
is in scope: the only things this development is allowed to assume outright are the
ones outside the raft protocol itself (the `Logger` interface, the tracing hooks,
`slices.Sort`, the RNG). The method lemmas below are therefore theorems -- several
still `sorry` in the files that state them, which marks them as *in scope and
unfinished* rather than assumed.

Lean notes:
* Rocq's `Context (cfg : gset w64)` is an explicit section variable `cfg`, so every
  definition and lemma that mentions it (`ownTracker`, `visitClosure`, the quorum and
  counting lemmas, ...) takes `cfg` as its first explicit argument, as Rocq's do once
  the section is closed.
* `elem_of_granted` is not restated: `Protocol.lean` already has it, with the same
  statement (in Rocq, `inv_tracker.v`'s copy shadows `protocol.v`'s).
* `wp_ProgressMap_len`: Perennial's Lean `wp_map_len` is stated at any type whose
  underlying type is a map (`[t ↓u go.MapType ..]`), so the proof is that lemma; the
  `go.len_underlying` detour the Rocq comment describes is not needed.
* `own_tracker_prvals_dom`: Rocq's `dom pvs = dom prs` is `domSet pvs = domSet prs`.
* The pure lemmas (quorum vocabulary, `nsat`) sit in their own section with only
  `cfg`, so they do not pick up the Go instance variables.
* `nsat` takes a decidable predicate (`[∀ k, Decidable (P k)]`, Rocq `Decision`), and
  `list_to_set keys` is `GMap.listToSet keys`.
* Rocq has two `Inflights` predicates whose Lean names would collide: the public
  `own_Inflights l i` (indexed by the record `Inflights`) is `ownInflights`, the
  internal `own_inflights l iv buf` (indexed by the Goose value and the ring buffer) is
  `ownInflightsRaw l r`, indexed instead by the pure record `r : InflightsRing` (the
  window, `start`, and the buffer's length). `own_Progress` is `ownProgress`;
  `progress_of` is `progressOf`;
  `inflights_full_abs` is `inflightsFull_abs`; `is_quorum_index` is `IsQuorumIndex`;
  `pvs_acked`/`pvs_match_at` are `pvsAcked`/`pvsMatchAt`; `own_progress_map` is
  `ownProgressMap`; `is_AckedIndexer` is `isAckedIndexer` (with a `Persistent`
  instance, which Rocq gets by `apply _` where it is used).
* `bool_decide (is_Some o)` is `o.isSome`.
-/
module

public import Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Two `ownMap`s at the same location describe the same map.

Not in `Perennial/Golang/Theory/Map.lean`, and provable there: `ownMap` is
`heapPointsto mref dq mv` plus `is_map_pure mv mp` plus a pointwise agreement between
`mp` and the `GMap`, and `go.mapLookup_pure` says `mapLookup mv k = mp k` -- so `mp` is
a function of `mv`, and the points-to pins `mv`. Stated here at `w64 ↦ Loc` because
that is where it is needed; lift it into the framework when a second caller appears. -/
theorem progress_map_agree (mref : Loc) (dq1 dq2 : DFrac) (m1 m2 : GMap w64 Loc) :
    ⊢ (mref ↦${dq1} m1 : IProp GF) -∗ mref ↦${dq2} m2 -∗ ⌜m1 = m2⌝ := by
  rw [ownMap_unseal]
  unfold ownMapDef
  iintro ⟨%mv1, %mp1, Hown1, %Hmap1, %Hag1, -⟩ ⟨%mv2, %mp2, Hown2, %Hmap2, %Hag2, -⟩
  ihave %Hmv := heapPointsto_agree _ _ _ _ _ $$ [Hown1 Hown2]
  · iframe Hown1 Hown2
  subst Hmv
  ipureintro
  apply GMap.map_eq; intro k
  have He1 := go.mapLookup_pure #k _ _ Hmap1
  have He2 := go.mapLookup_pure #k _ _ Hmap2
  have Heq : mp1 #k = mp2 #k := He1.symm.trans He2
  rw [Hag1 k, Hag2 k] at Heq
  cases h1 : m1 !! k <;> cases h2 : m2 !! k <;> simp only [h1, h2] at Heq
  · rfl
  · cases Heq
  · cases Heq
  · simp only [Prod.mk.injEq, true_and] at Heq
    rw [go.intoVal_inj Heq]

-- The (fixed) set of voters.
variable (cfg : GSet w64)

-- The (fixed) set of voters.
variable (cfg : GSet w64)

/-! ### Inflights

A sliding window of in-flight append sizes. Callers see it through the public record
`Inflights` (how many messages and bytes are in flight, and the two limits): enough to
state `Full`, `Add`, `FreeLE`, `reset` and `NewInflights` exactly. The ring (`start` and
the buffer) is internal (`InflightsRing`), and the buffer's contents are in no index at
all -- no spec states them. -/

/-- `Full()`'s answer (`inflightsFull`, `Defs.lean`), read off the `Inflights` value
(`Inflights.Full.impl`, `Code/go_etcd_io/raft/v3/tracker.lean`):

    in.count == in.size || (in.maxBytes != 0 && in.bytes >= in.maxBytes)

`Inflights.Add` **panics** when it is `true` ("cannot add into a Full inflights"), so
`Add`'s triple can only be stated -- truthfully -- at a window the caller knows is not
full. That is why `ownInflights` is indexed by a record that determines it. (Until
2026-10-02 `inflightsFull` was this right-hand side, on the Goose value.) -/
theorem inflightsFull_abs (iv : tracker.Inflights) :
    inflightsFull (inflightsAbs iv) =
      (decide (iv.count' = iv.size') ||
        (decide (iv.maxBytes' ≠ W64 0) && decide (uint.Z iv.maxBytes' ≤ uint.Z iv.bytes'))) := by
  unfold inflightsFull inflightsAbs
  have h1 : decide (sint.Z iv.count' = sint.Z iv.size') = decide (iv.count' = iv.size') :=
    decide_eq_decide.2 BitVec.toInt_inj
  have h2 : decide (uint.Z iv.maxBytes' ≠ 0) = decide (iv.maxBytes' ≠ W64 0) := by
    apply decide_eq_decide.2
    constructor
    · intro h hc; apply h; rw [hc]; rfl
    · intro h hc; apply h; exact uint_Z_inj.1 (by rw [hc]; rfl)
  simp only [h1, h2]

/-- The internal state of an `Inflights` object: exactly what the internal spec (`grow`'s,
the only one) needs, and nothing of the Go struct beyond it -- the public window `win`
(`count`, `size`, `bytes`, `maxBytes`), the ring position `start`, and the *length*
`buflen` of the ring buffer, all as the integers they denote. `grow` is about the
length; `start` is there because `Add`, after a `grow`, needs it unchanged. Neither
the buffer's address nor its contents is in it: no spec says anything about them
(`FreeLE` reads the contents, but its spec is a relation on `win`).

One record rather than separate arguments, and as small as the specs allow, so that
`InflightsOk`, `ownInflightsRaw` and the specs stated on them keep their arity when a
piece of state is added or dropped; specs write a new state as an update
(`{ r with buflen := n }`), which survives a new field too. (Until 2026-10-08 the
predicate took the Goose value and the buffer's contents as two arguments, as Rocq's
`own_inflights l iv buf` does.) -/
structure InflightsRing where
  win : Inflights
  start : Int
  buflen : Int

/-- The state a Goose value and its buffer's contents denote. -/
def inflightsRingOf (iv : tracker.Inflights) (buf : List tracker.inflight) : InflightsRing :=
  ⟨inflightsAbs iv, sint.Z iv.start', buf.length⟩

/-- The ring-buffer invariant.

`Add` writes `buffer[(start+count) mod size]` after growing the buffer on demand, so a
triple for it is false without this: with, say, `start = 100`, `count = 0`,
`size = 1000` and an empty buffer, `Add` is not `Full`, grows the buffer to one slot
and then indexes slot 100 -- out of range. The conjuncts, in order: `start` and
`count` are non-negative, `count` fits the ring, the buffer is at most the ring, the
ring is small enough that `len(buffer) * 2` in `grow` cannot overflow, `start` is a
ring position (degenerately `0` when the ring is empty), and **every occupied slot is
inside the buffer** -- either the occupied range does not wrap, or the buffer has
already grown to the full ring.

Note `0 ≤ buflen ≤ size` forces `0 ≤ size`, so a degenerate `size = 0` ring is pinned
to `start = count = buflen = 0`; that ring is always `Full`, so `Add` is unreachable
on it. -/
def InflightsOk (r : InflightsRing) : Prop :=
  0 ≤ r.start ∧
  (0 ≤ r.win.count ∧ r.win.count ≤ r.win.size) ∧
  (0 ≤ r.buflen ∧ r.buflen ≤ r.win.size) ∧
  r.win.size < 2 ^ 62 ∧
  (r.start < r.win.size ∨ (r.win.size = 0 ∧ r.start = 0)) ∧
  (r.start + r.win.count ≤ r.buflen ∨ r.buflen = r.win.size)

/-- The **internal** predicate for an `Inflights` object, indexed by its state `r`
(`InflightsRing`): the Goose value and the buffer's contents are existential, and
denote `r`. Only `Inflights`' own methods see it: `grow` is stated on it, and the other
methods' proofs open `ownInflights` to it. A proof that opens it gets `r` as
`inflightsRingOf iv buf` (`subst Hring`) and works on the Goose value; one that closes
it uses `ownInflightsRaw_intro`. (Until 2026-10-02 this was the one predicate, and
every caller's spec named the Goose value; until 2026-09-23 there were two forms,
`own_inflights_at l iv` and the existential `own_inflights l`; notes/decisions.md,
"Three layers".) -/
def ownInflightsRaw (l : Loc) (r : InflightsRing) : IProp GF :=
  iprop(∃ (iv : tracker.Inflights) (buf : List tracker.inflight),
    "Hiv" ∷ l ↦ iv ∗
    "Hbuf" ∷ iv.buffer' ↦* buf ∗
    "Hbuf_cap" ∷ ownSliceCap tracker.inflight iv.buffer' (DFrac.own 1) ∗
    "%Hring" ∷ ⌜r = inflightsRingOf iv buf⌝ ∗
    "%Hinfl_ok" ∷ ⌜InflightsOk r⌝)

/-- Close `ownInflightsRaw` at the state the pieces denote. The pure premise is last,
so that `iapply ownInflightsRaw_intro $$ Hiv Hbuf Hbuf_cap` fixes the value and the
contents from the hypotheses (and with them a state left open, as in a postcondition's
existential) and leaves the ring invariant as the goal. -/
theorem ownInflightsRaw_intro (l : Loc) (iv : tracker.Inflights)
    (buf : List tracker.inflight) :
    ⊢ (l ↦ iv : IProp GF) -∗ iv.buffer' ↦* buf -∗
      ownSliceCap tracker.inflight iv.buffer' (DFrac.own 1) -∗
      ⌜InflightsOk (inflightsRingOf iv buf)⌝ -∗
      ownInflightsRaw l (inflightsRingOf iv buf) := by
  iintro Hiv Hbuf Hbuf_cap %Hok
  unfold ownInflightsRaw
  iexists iv, buf
  simp only [named]
  iframe Hiv Hbuf Hbuf_cap
  ipureintro
  constructor <;> first | trivial | exact Hok

/-- The **public** predicate for an `Inflights` object, indexed by the record
`Inflights` (`Defs.lean`): how many messages and bytes are in flight, and the two
limits -- exactly what the exported methods' specs (`Full`, `Add`, `FreeLE`, `reset`,
`NewInflights`) say. The ring (`start` and the buffer) is hidden. -/
def ownInflights (l : Loc) (i : Inflights) : IProp GF :=
  iprop(∃ (r : InflightsRing),
    "Hin" ∷ ownInflightsRaw l r ∗
    "%Hiabs" ∷ ⌜r.win = i⌝)

theorem ownInflights_intro (l : Loc) (r : InflightsRing) :
    ⊢ ownInflightsRaw (GF := GF) l r -∗ ownInflights l r.win := by
  iintro Hin
  unfold ownInflights
  iexists r
  simp only [named]
  iframe Hin

/-- Close `ownInflights` from the pieces of an opened `ownInflightsRaw`. The pure
premise is last, so that `iapply ownInflights_reseal $$ Hiv Hbuf Hbuf_cap` fixes the
value and the contents from the hypotheses and leaves the ring invariant and the
window as one pure goal. -/
theorem ownInflights_reseal (l : Loc) (iv : tracker.Inflights)
    (buf : List tracker.inflight) (i : Inflights) :
    ⊢ (l ↦ iv : IProp GF) -∗ iv.buffer' ↦* buf -∗
      ownSliceCap tracker.inflight iv.buffer' (DFrac.own 1) -∗
      ⌜InflightsOk (inflightsRingOf iv buf) ∧ inflightsAbs iv = i⌝ -∗
      ownInflights l i := by
  iintro Hiv Hbuf Hbuf_cap %H
  obtain ⟨Hok, rfl⟩ := H
  rw [show inflightsAbs iv = (inflightsRingOf iv buf).win from rfl]
  iapply ownInflights_intro l (inflightsRingOf iv buf)
  iapply ownInflightsRaw_intro l iv buf $$ Hiv Hbuf Hbuf_cap
  ipureintro; exact Hok

/-! ### Per-peer replication progress

Ownership is of the whole `Progress` *value*, because `reset`'s `Visit` closure
overwrites one wholesale (`pr <-[tracker.Progress] CompositeLiteral ...`); a predicate
over selected fields could not justify that write. What hangs off the value is its
`Inflights` object.

A field assignment like `becomeLeader`'s `pr.RecentActive := true` steps through
`pr ↦ pv` with the generated `AccessStrict` instances and leaves `Inflights'` alone,
so `ownInflightsRaw` survives it untouched. -/

/-- The **public** predicate for a `Progress` object, indexed by the record `Progress`
(`Defs.lean`), which includes its `Inflights` window `infl`. `IsPaused`'s answer is a
function of `state` and `paused`, and `SentEntries` reaches `Inflights.Add`, whose
precondition is `inflightsFull infl = false`.

`progressAbs pv infl = some p` says what the two pure conjuncts of the old
`own_progress pr pv iv` said (until 2026-10-02), and more:

- **not a learner** (`IsLearner = false`): no learners are in scope. Added 2026-09-16
  because `raft.wp_promotable` needs it: `promotable` returns
  `pr != nil && !pr.IsLearner && ...`, and without it its postcondition
  `b = decide (id ∈ cfg)` is not derivable.
- **the state is one of the three** (`StateProbe`/`StateReplicate`/`StateSnapshot`):
  `Progress.IsPaused` **panics** on anything else ("unexpected state", tracker.v:456),
  and `bcastAppend` reaches it on every peer. `reset`'s `Visit` closure writes a
  literal with no `State` field, i.e. the zero value `StateProbe`, and `ResetState` is
  always passed one of the three.

A field assignment like `becomeLeader`'s `pr.RecentActive := true` steps through
`Hpv` with the generated `AccessStrict` instances and leaves `Inflights'` alone.
Ownership is of the whole `Progress` *value*, because `reset`'s `Visit` closure
overwrites one wholesale. -/
def ownProgress (pr : Loc) (p : Progress) : IProp GF :=
  iprop(∃ (pv : tracker.Progress),
    "Hpv" ∷ pr ↦ pv ∗
    "Hinfl" ∷ ownInflights pv.Inflights' p.infl ∗
    "%Habs" ∷ ⌜progressAbs pv p.infl = some p⌝)

/-- Re-seal `ownProgress` after field writes: the record read off the value. The pure
premise is last, so that `iapply ownProgress_intro … $$ Hpv Hinfl` fixes the value from
`Hpv` and leaves `progressAbs pv' p.infl = some p` to `progress_abs_solve`. -/
theorem ownProgress_intro (pr : Loc) (pv : tracker.Progress) (p : Progress) :
    ⊢ pr ↦ pv -∗ ownInflights (GF := GF) pv.Inflights' p.infl -∗
      ⌜progressAbs pv p.infl = some p⌝ -∗ ownProgress pr p := by
  iintro Hpv Hinfl %Habs
  unfold ownProgress
  iexists pv
  simp only [named]
  iframe Hpv Hinfl
  ipureintro; exact Habs

/-- The same, at the record read off the value: for a `Progress` written wholesale
(`reset`'s `Visit` closure) or field by field, when the caller wants the record to be
whatever the value says. -/
def progressOf (pv : tracker.Progress) (st : PRState) (i : Inflights) : Progress :=
  ⟨pv.Match', pv.Next', pv.sentCommit', st, pv.PendingSnapshot', pv.MsgAppFlowPaused', i⟩

theorem ownProgress_of (pr : Loc) (pv : tracker.Progress) (st : PRState) (i : Inflights)
    (Hl : pv.IsLearner' = false) (Hst : pv.State' = prstateW64 st) :
    ⊢ pr ↦ pv -∗ ownInflights (GF := GF) pv.Inflights' i -∗
      ownProgress pr (progressOf pv st i) := by
  iintro Hpv Hinfl
  unfold ownProgress
  iexists pv
  simp only [named, progressOf]
  iframe Hpv Hinfl
  ipureintro
  exact (progressAbs_Some _ _ _).2 ⟨Hl, Hst, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An id set (`map[uint64]struct{}`) that is either `nil` or owned.

`ownTracker` used to say `Learners ↦$ learners` outright, and a map points-to implies
a non-nil location (`ownMap_not_nil`, `Perennial/Golang/Theory/Map.lean`). But the
tracker `newRaft` builds has `Learners = LearnersNext = nil`: `MakeProgressTracker`
writes `nil` ("only populated when used"), `Config.Clone` maps `nil` to `nil`, and only
adding a *learner* ever allocates one. So until 2026-09-22 `ownTracker` -- and with it
`ownRaftPhys` -- was **unsatisfiable by any raft `newRaft` returns**. Found by writing
`newRaft`'s spec; nothing on the election path reads either map, so the weakening
costs no proof anything. -/
def ownIdsetOpt (m : Loc) (ids : GMap w64 Unit) : IProp GF :=
  iprop(⌜m = map.nil ∧ ids = ∅⌝ ∨ m ↦$ ids)

/-! ### The progress tracker

`trk` is embedded in the raft struct **by value**, so the tracker's own bytes are part
of the `r ↦ rv` clause of `ownRaftPhys` and must not be claimed a second time.
`ownTracker cfg tv t` therefore owns exactly what the tracker *value* `tv` points at:
the vote map, the progress map together with the `Progress` objects in it, and the id
sets of the configuration.

The configuration is *simple*, not joint -- no reconfiguration and no learners are in
scope -- which is recorded the same way `readonly.lean` records it: the `JointConfig`
array is `[voters_ref, map.nil]`. The voter set and the domain of the progress map are
both `cfg`.

It is indexed by one record `t : Trk` (`Defs.lean`): the tally `t.votes`, the progress
map `t.prs`, and `t.peers`, what each `Progress` holds, by peer (`NState.prvals`):
`prs` and `peers` are paired key by key, so they have the same domain. (Until
2026-10-02 the three were separate arguments and `peers` held Goose values; until
2026-09-29 the values were existential inside, and a caller that needed one across a
call it made with the struct sealed had to take the tracker out of `ownRaftPhys` on
loan.) -/
def ownTracker (tv : tracker.ProgressTracker) (t : Trk) : IProp GF :=
  iprop(∃ (voters_ref : Loc) (voters : GMap w64 Unit)
    (learners learnersNext : GMap w64 Unit),
  "Hvotes" ∷ tv.Votes' ↦$ t.votes ∗
  -- **Read-only.** The progress *map* is allocated once, by `newTracker`/`confchange`,
  -- and on the election path nothing ever inserts into it or deletes from it -- only
  -- the `Progress` *values* it points at are written (`reset`'s `Visit` closure,
  -- `BecomeReplicate`, `SentEntries`). Holding it at `DFrac.discard` records that, and
  -- buys the one thing an exclusive points-to cannot: the map is **duplicable**, so a
  -- proof can keep a copy of `⌜prs !! to = some pr⌝` across a call that consumes and
  -- rebuilds the whole tracker. `maybeSendAppend` needs exactly that -- it holds the
  -- raw `pr` pointer across `r.send(...)`, which is specified on `ownRaftPhys` and so
  -- takes the tracker with it, and must then call `pr.SentEntries`/`pr.SentCommit` on
  -- the *same* pointer. With an existentially quantified exclusive map there is no way
  -- back to that pointer; see `ownTracker_lookup` below. Changed 2026-09-20.
  --
  -- It is a genuine restriction: a proof of a reconfiguration path would have to take
  -- the map back to `DFrac.own 1`. Reconfiguration is out of scope (see
  -- `HnoConfChange` in `InvRaftlog.lean`).
  "#Hprs" ∷ tv.Progress' ↦$□ t.prs ∗
  "Hprogs" ∷ ([∗map] _k ↦ pr;p ∈ t.prs;t.peers, ownProgress pr p) ∗
  "%Hprs_dom" ∷ ⌜domSet t.prs = cfg⌝ ∗
  -- a simple configuration: second component of the joint config is nil
  "%Hvoters_arr" ∷ ⌜tv.Config'.Voters'.arr = [voters_ref, map.nil]⌝ ∗
  -- and not a joint one on its way out: `AutoLeave` is only set on entering a joint
  -- configuration. `ConfState` reads it (added 2026-09-29, when `switchToConfig`
  -- stopped keeping the tracker value in hand across the call)
  "%Hautoleave" ∷ ⌜tv.Config'.AutoLeave' = false⌝ ∗
  "Hvoters" ∷ voters_ref ↦$ voters ∗
  "%Hvoters_dom" ∷ ⌜domSet voters = cfg⌝ ∗
  -- no learners. Either map may be `nil` -- and after `newRaft` both are: see
  -- `ownIdsetOpt`.
  "Hlearners" ∷ ownIdsetOpt tv.Config'.Learners' learners ∗
  "HlearnersNext" ∷ ownIdsetOpt tv.Config'.LearnersNext' learnersNext ∗
  "%Hno_learners" ∷ ⌜learners = ∅ ∧ learnersNext = ∅⌝ ∗
  -- `campaign` does `make([]uint64, 0, len(idMap))`, and `wp_slice_make3` needs
  -- `0 ≤ sint.Z cap`; `campaign`, `Visit`, `VoterNodes` and `CommittedIndex` then
  -- `slices.Sort` the voter ids, which needs at most `2^62` of them (past that its
  -- heapsort fallback overflows `int`). Nothing else bounds the voter set: no Iris
  -- ownership constrains the cardinality of a `GSet w64`, so `size cfg = 2^64` is
  -- consistent with every other conjunct here. This is a property of the
  -- configuration, so it belongs with the configuration (`newRaft` takes it as a
  -- premise about the storage's initial `ConfState`).
  "%Hcfg_size" ∷ ⌜(GMap.size cfg : Int) ≤ 2 ^ 62⌝ ∗
  -- **No non-emptiness conjunct.** From 2026-09-16 to 2026-09-29 this predicate
  -- required `cfg ≠ ∅`, because `MajorityConfig.VoteResult` returns `VoteWon` outright
  -- for an empty configuration while `IsQuorum ∅ q` is false. That made the *empty*
  -- tracker `MakeProgressTracker` builds -- the one `newRaft` starts from -- not an
  -- `ownTracker`, so `newRaft` had to hold it on loan until `switchToConfig`. The
  -- premise now sits where it is used: `JointConfig.VoteResult`, `TallyVotes` and
  -- `poll` take `cfg ≠ ∅`.
  --
  -- **The inflight window is a sane size.** `Config.validate` requires only
  -- `MaxInflightMsgs > 0` -- **it has no upper bound** (this comment said `(0, 1<<30]`
  -- until 2026-09-24; notes/false-statements.md) -- and `newRaft` copies it into the
  -- tracker, so the `< 2^62` half is an extra premise of `newRaft`'s spec, not
  -- something raft checks. So this predicate excludes valid configs with
  -- `MaxInflightMsgs ≥ 2^62`. Needed because `reset`'s `Visit` closure calls
  -- `tracker.NewInflights(r.trk.MaxInflight, …)`, and the ring-buffer invariant of
  -- `ownInflightsRaw` pins `0 ≤ size < 2^62` (see `InflightsOk`). Like `Hcfg_size` it
  -- is a property of the configuration and is never written on the election path.
  -- Added 2026-09-20 for `bcastAppend`.
  "%HmaxInfl" ∷ ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝)

/-- Re-sealing a tracker a proof has taken apart, as one `iapply`:

    iapply ownTracker_intro … $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

(In Rocq, `iExists …; iFrame "∗#%"` against the unfolded predicate cost ~30s per use
in a proof body; notes/gotchas.md.) The pure premises are in the order the conjuncts
appear in `ownTracker`. The conclusion is at `⟨votes, prs, peers⟩`, so that the
hypotheses fix the three maps (in Lean `Trk` has definitional eta, so a goal at a
variable `t` unifies with it). -/
theorem ownTracker_intro (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (peers : GMap w64 Progress)
    (voters_ref : Loc) (voters learners learnersNext : GMap w64 Unit)
    (Hprs_dom : domSet prs = cfg)
    (Hvoters_arr : tv.Config'.Voters'.arr = [voters_ref, map.nil])
    (Hautoleave : tv.Config'.AutoLeave' = false)
    (Hvoters_dom : domSet voters = cfg)
    (Hno_learners : learners = ∅ ∧ learnersNext = ∅)
    (Hcfg_size : (GMap.size cfg : Int) ≤ 2 ^ 62)
    (HmaxInfl : 0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62) :
    ⊢ (tv.Votes' ↦$ votes : IProp GF) -∗
      tv.Progress' ↦$□ prs -∗
      ([∗map] _k ↦ pr;p ∈ prs;peers, ownProgress pr p) -∗
      voters_ref ↦$ voters -∗
      ownIdsetOpt tv.Config'.Learners' learners -∗
      ownIdsetOpt tv.Config'.LearnersNext' learnersNext -∗
      ownTracker cfg tv ⟨votes, prs, peers⟩ := by
  unfold ownTracker
  iintro Hvotes #Hprs Hprogs Hvoters Hlearners HlearnersNext
  iexists voters_ref, voters, learners, learnersNext
  simp only [named]
  iframe Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext
  ipureintro
  exact ⟨Hprs_dom, Hvoters_arr, Hautoleave, Hvoters_dom, Hno_learners, Hcfg_size, HmaxInfl⟩

end proof

section pure
-- The (fixed) set of voters.
variable (cfg : GSet w64)

/-! ### Pure facts about the quorum vocabulary

`TallyVotes` has to connect what the Go code counts to what the model says. These
lemmas are the bridge, and they are pure Lean -- no program, no ownership -- so they
are stated here rather than inside a proof. `IsQuorum`, `granted` and `rejected` are
from `Protocol/Model.lean` (and `elem_of_granted` from `Protocol/GhostState.lean`). -/

theorem elem_of_rejected (votes : GMap w64 Bool) (k : w64) :
    k ∈ rejected votes ↔ votes !! k = some false := by
  unfold rejected
  rw [GMap.elem_of_dom]
  constructor
  · rintro ⟨b, Hb⟩
    rw [GMap.mapLookup_filter_Some] at Hb
    obtain ⟨Hv, Hb⟩ := Hb
    cases b
    · exact Hv
    · exact absurd Hb (by decide)
  · intro Hv
    exact ⟨false, (GMap.mapLookup_filter_Some _ _ _ _).mpr ⟨Hv, rfl⟩⟩

/-- Go computes the majority threshold as `q := len(c)/2 + 1` and tests
`votedCnt >= q`; the model says `size cfg < 2 * size (q ∩ cfg)`. They agree, integer
division and all. -/
theorem IsQuorum_alt (q : GSet w64) :
    IsQuorum cfg q ↔ GMap.size cfg / 2 + 1 ≤ GMap.size (q ∩ cfg) := by
  unfold IsQuorum; omega

/-- A voter that has not rejected has either granted or not answered, which is why
`MajorityConfig.VoteResult`'s `votedCnt + missing` is exactly
`size (cfg \ rejected votes)` -- the quantity `Step.lose` talks about. -/
theorem cfg_minus_rejected (votes : GMap w64 Bool) :
    cfg \ rejected votes = (granted votes ∩ cfg) ∪ (cfg \ domSet votes) := by
  apply GMap.set_eq; intro k
  rw [GMap.elem_of_union, GMap.elem_of_intersection, GMap.elem_of_difference,
    GMap.elem_of_difference, elem_of_granted, elem_of_rejected, GMap.elem_of_dom]
  cases votes !! k with
  | none => simp
  | some b => cases b <;> simp

theorem granted_missing_disjoint (votes : GMap w64 Bool) :
    (granted votes ∩ cfg) ## (cfg \ domSet votes) := by
  rw [GMap.elem_of_disjoint]
  intro k Hk1 Hk2
  rw [GMap.elem_of_intersection, elem_of_granted] at Hk1
  rw [GMap.elem_of_difference, GMap.elem_of_dom] at Hk2
  exact Hk2.2 ⟨true, Hk1.1⟩

theorem size_cfg_minus_rejected (votes : GMap w64 Bool) :
    GMap.size (cfg \ rejected votes) =
      GMap.size (granted votes ∩ cfg) + GMap.size (cfg \ domSet votes) := by
  rw [cfg_minus_rejected, GMap.size_union (granted_missing_disjoint cfg votes)]

/-! ### Counting along a map enumeration

`wp_map_for_range` (`Perennial/Golang/Theory/Map.lean`) hands the proof an arbitrary
duplicate-free enumeration `keys` of the map's domain and an index `i` into it, so a
loop that counts has to count over a *list*. `nsat` is that count; `nsat_size`
converts it back to a set cardinality once the range is over. -/

def nsat (P : w64 → Prop) [∀ k, Decidable (P k)] (l : List w64) : Nat :=
  (l.filter (fun k => decide (P k))).length

theorem nsat_snoc (P : w64 → Prop) [∀ k, Decidable (P k)] (l : List w64) (k : w64) :
    nsat P (l ++ [k]) = nsat P l + (if P k then 1 else 0) := by
  unfold nsat; rw [List.filter_append]; by_cases h : P k <;> simp [h]

theorem nsat_le (P : w64 → Prop) [∀ k, Decidable (P k)] (l : List w64) :
    nsat P l ≤ l.length := by
  unfold nsat; exact List.length_filter_le _ _

theorem nsat_size (Y : GSet w64) (keys : List w64) (P : w64 → Prop) [∀ k, Decidable (P k)]
    (HY : ∀ k, k ∈ cfg → (k ∈ Y ↔ P k)) (Hsub : Y ⊆ cfg) (Hnd : keys.Nodup)
    (Hset : GMap.listToSet keys = cfg) :
    nsat P keys = GMap.size Y := by
  unfold nsat
  rw [← GMap.size_list_to_set _ (Hnd.filter _)]
  congr 1
  apply GMap.set_eq; intro k
  rw [GMap.elem_of_list_to_set, List.mem_filter, decide_eq_true_iff]
  constructor
  · rintro ⟨Hk, HP⟩
    have Hkc : k ∈ cfg := by rw [← Hset, GMap.elem_of_list_to_set]; exact Hk
    exact (HY k Hkc).2 HP
  · intro HkY
    have Hkc : k ∈ cfg := (GMap.elem_of_subseteq _ _).1 Hsub k HkY
    refine ⟨?_, (HY k Hkc).1 HkY⟩
    rw [← GMap.elem_of_list_to_set, Hset]; exact Hkc

theorem nsat_granted (votes : GMap w64 Bool) (keys : List w64)
    (Hnd : keys.Nodup) (Hset : GMap.listToSet keys = cfg) :
    nsat (fun k => votes !! k = some true) keys = GMap.size (granted votes ∩ cfg) := by
  apply nsat_size cfg _ _ _ _ _ Hnd Hset
  · intro k Hk; rw [GMap.elem_of_intersection, elem_of_granted]; exact ⟨fun h => h.1, fun h => ⟨h, Hk⟩⟩
  · rw [GMap.elem_of_subseteq]; intro k Hk; exact ((GMap.elem_of_intersection _ _ _).1 Hk).2

theorem nsat_rejected (votes : GMap w64 Bool) (keys : List w64)
    (Hnd : keys.Nodup) (Hset : GMap.listToSet keys = cfg) :
    nsat (fun k => votes !! k = some false) keys = GMap.size (rejected votes ∩ cfg) := by
  apply nsat_size cfg _ _ _ _ _ Hnd Hset
  · intro k Hk; rw [GMap.elem_of_intersection, elem_of_rejected]; exact ⟨fun h => h.1, fun h => ⟨h, Hk⟩⟩
  · rw [GMap.elem_of_subseteq]; intro k Hk; exact ((GMap.elem_of_intersection _ _ _).1 Hk).2

theorem nsat_missing (votes : GMap w64 Bool) (keys : List w64)
    (Hnd : keys.Nodup) (Hset : GMap.listToSet keys = cfg) :
    nsat (fun k => votes !! k = none) keys = GMap.size (cfg \ domSet votes) := by
  apply nsat_size cfg _ _ _ _ _ Hnd Hset
  · intro k Hk; rw [GMap.elem_of_difference, GMap.not_elem_of_dom]; exact ⟨fun h => h.2, fun h => ⟨Hk, h⟩⟩
  · rw [GMap.elem_of_subseteq]; intro k Hk; exact ((GMap.elem_of_difference _ _ _).1 Hk).1

end pure

section proof2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- The (fixed) set of voters.
variable (cfg : GSet w64)

/-- `len` of a *named* map type.

In Rocq, `new/golang/defn/map.v` declares its `FuncUnfold` instances at
`go.MapType key_type elem_type` literally, so `wp_auto` could not step
`len(p.Progress)`, whose static type is the named `tracker.ProgressMap`, and the way
through was `go.len_underlying`. Perennial's Lean `wp_map_len` is already stated at
any type whose underlying type is a map, so here it is a direct instance.

Used by `Visit`; kept here because working this out is the sort of thing one should
not have to do twice. -/
theorem wp_ProgressMap_len (mref : Loc) (dq : DFrac) (m : GMap w64 Loc) :
    {{ (mref ↦${dq} m : IProp GF) }}
      (App (Val #(functions go.len [tracker.ProgressMap.ty])) (Val #mref))
    {{ RET #(W64 (GMap.size m)); mref ↦${dq} m }} :=
  wp_map_len mref m dq

/-- `trk.Visit f` calls `f id pr` on every voter's `Progress`.

The closure is handed full ownership of one `Progress`, the tracker field `trk ↦ tv`,
a wand that turns that `Progress` back into the **whole** tracker, and whatever the
caller lends it (`I`). It gives back the tracker (not the lone `Progress`), the field
and `I`. `reset`'s closure needs the first three: it overwrites the `Progress`, reads
`r.trk.MaxInflight` and `r.trk.MaxInflightBytes` through the field, and reads
`r.raftLog` and `r.id` through `I`; it applies the wand at the end.

**Why the wand, and why the tracker comes back whole** (changed 2026-09-20 for
`bcastAppend`). `bcastAppend`'s closure calls `r.sendAppend(id)`, which reaches
`maybeSendAppend`; that function looks the peer up in `r.trk.Progress` *itself* and
then calls `r.send`, whose triple is stated on `ownRaftPhys` -- which contains
`ownTracker`. So the closure needs the entire tracker, not one `Progress` out of it,
and with only `ownProgress pr` in hand it could not even step the `map.lookup1`.
Handing it `ownProgress pr` *plus* the accessor wand costs `Visit` nothing (it does its
own lookup before each call and does not touch the map during one) and leaves
`reset`'s closure free to keep using the lone `Progress`. The postcondition asks only
for the tracker back because a closure that has already merged the `Progress` into it
-- as `bcastAppend`'s must -- cannot split the same one out again: nothing in
`ownTracker` says which key `pr` sits at.

The `i ∈ cfg` premise is likewise for `bcastAppend`: its closure calls
`r.sendAppend(id)`, and `maybeSendAppend` looks `id` up in the progress map itself,
which only hits for a voter. `Visit` has it -- it only enumerates keys of `prs`, whose
domain is `cfg`.

**Why the tracker value may change** (`tv` is quantified per call, and the closure
gives back some `tv'`, possibly different). This is not generality for its own sake;
without it `bcastAppend` is not provable. Its closure has to run `r.sendAppend(id)`,
whose triple -- like every triple below `raft.send` -- is stated on `ownRaftPhys`,
which packages the *whole* struct as `∃ rv, r ↦ rv ∗ …`. So the closure must merge the
lent `trk ↦ tv` back into `r ↦ rv` before the call, and what comes back is a fresh,
existentially quantified `rv'`. Nothing in `ownRaftPhys` ties `rv'.trk'` to `tv` --
`send` does not touch the field, but its *spec* cannot say so -- so a closure obliged
to return the field at the original `tv` would be stuck. Returning it at whatever
value the rebuilt struct has costs `Visit` nothing: it re-reads `p.Progress` through
the field on every iteration anyway, and all it needs of the tracker is
`domSet prs = cfg`, which `ownTracker` gives at any `tv'`. `reset`'s closure simply
returns the `tv` it was handed.

The `MaxInflight` bound comes along for the same reason. `reset`'s closure calls
`NewInflights(r.trk.MaxInflight, …)`, whose premise it is (`InflightsOk`, above); with
the tracker value quantified per call the closure can no longer read that bound out of
the enclosing proof's context, and it cannot read it out of `ownTracker` either -- it
holds the tracker only as a wand, and cashing that wand costs it the `ownProgress` it
is there to overwrite. So `Visit`, which does hold the tracker, hands the fact over.

**Why the progress map stays fixed** (`prs`). The tracker value may change, but the
progress map may not: nothing on the election path inserts into or deletes from it,
and `ownTracker` is indexed by it (2026-09-23), so the closure hands the tracker back
at the same `prs` and `Visit` promises the same of itself. That is what lets `reset`
-- which runs `Visit` -- re-establish `ownRaftPhys`, whose tracker is at
`NState.progress`.

**Why the field is lent rather than kept.** `Visit` itself reads `p.Progress` on every
iteration, so it cannot hand the field over for good; and the closure reads a
*different* sub-field of the same value, so it cannot be denied it. The two reads are
at different times, so lending resolves it. See `spec_ProgressTracker__Visit.v` for
how this was got wrong.

**The caller invariant is indexed** (2026-10-01) by the set `D` of ids visited so far
and the tracker's current `Progress` values: the closure takes `I D pvs` to
`I ({[i]} ∪ D) pvs'`. `reset` needs both -- its postcondition says what `Match` every
voter ends with, which is a fact about every key, and about the values the tracker
holds -- and `Visit` ends at `I cfg`. -/
def visitClosure (trk : Loc) (votes : GMap w64 Bool) (prs : GMap w64 Loc) (f : GoFunc)
    (I : GSet w64 → GMap w64 Progress → IProp GF) : IProp GF :=
  iprop(∀ (i : w64) (pr : Loc) (tv : tracker.ProgressTracker)
      (pvs : GMap w64 Progress) (p : Progress) (D : GSet w64),
    {{ ⌜i ∈ cfg⌝ ∗ ⌜prs !! i = some pr⌝ ∗ ⌜pvs !! i = some p⌝ ∗
        ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗
        trk ↦ tv ∗ ownProgress pr p ∗
        (∀ p', ownProgress pr p' -∗ ownTracker cfg tv ⟨votes, prs, <[i := p']> pvs⟩) ∗
        I D pvs }}
      (App (App (Val #f) (Val #i)) (Val #pr))
    {{ RET #(); ∃ tv' pvs', trk ↦ tv' ∗ ownTracker cfg tv' ⟨votes, prs, pvs'⟩ ∗
                            I ({[i]} ∪ D) pvs' }})

/-- The inflight-window bound, read out without consuming the tracker. `reset`'s
`Visit` closure calls `tracker.NewInflights(r.trk.MaxInflight, ...)`, whose premise
this is; the closure cannot reach `ownTracker` itself, so `reset` pulls the fact into
the Lean context before the `Visit`. -/
theorem ownTracker_maxinflight (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTracker (GF := GF) cfg tv t -∗
      ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗
      ownTracker cfg tv t := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  isplitr
  · ipureintro; exact HmaxInfl
  iapply ownTracker_intro cfg tv t.votes t.prs t.peers voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

/-- The configuration has at most `2^62` voters (`Hcfg_size`); the tracker survives. -/
theorem ownTracker_size (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTracker (GF := GF) cfg tv t -∗
      ⌜(GMap.size cfg : Int) ≤ 2 ^ 62⌝ ∗ ownTracker cfg tv t := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  isplitr
  · ipureintro; exact Hcfg_size
  iapply ownTracker_intro cfg tv t.votes t.prs t.peers voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

/-- Borrow one voter's `Progress` out of the tracker, by its key in the progress map
the tracker is indexed by, at the record `t.peers` holds for it; give it back at any
record, which the index then records. The caller can come back to the *same* pointer,
and the same record, after any call that returns the tracker at the same `prs` and
`peers`. -/
theorem ownTracker_lookup (tv : tracker.ProgressTracker) (t : Trk) (i : w64) (pr : Loc)
    (Hpr : t.prs !! i = some pr) :
    ⊢ ownTracker (GF := GF) cfg tv t -∗
      ∃ p, ⌜t.peers !! i = some p⌝ ∗ ownProgress pr p ∗
        (∀ p', ownProgress pr p' -∗
               ownTracker cfg tv ⟨t.votes, t.prs, <[i := p']> t.peers⟩) := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  obtain ⟨p, Hv⟩ := Option.isSome_iff_exists.1
    ((Hiff i).1 (by show (t.prs !! i).isSome = true; rw [Hpr]; rfl))
  icases BigSepM2.bigSepM2_insert_acc (Φ := fun _ pr p => ownProgress (GF := GF) pr p)
    (m1 := t.prs) (m2 := t.peers) Hpr Hv $$ Hprogs with ⟨Hp, Hback⟩
  iexists p
  isplitr
  · ipureintro; exact Hv
  iframe Hp
  iintro %p' Hp
  ihave Hprogs := Hback $$ %pr %p' Hp
  have Hins : (Iris.Std.PartialMap.insert t.prs i pr : GMap w64 Loc) = t.prs :=
    GMap.insert_id t.prs i pr Hpr
  rw [Hins]
  iapply ownTracker_intro cfg tv t.votes t.prs _ voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

/-- The same, given back at the record it was borrowed at. -/
theorem ownTracker_lookup_same (tv : tracker.ProgressTracker) (t : Trk) (i : w64) (pr : Loc)
    (Hpr : t.prs !! i = some pr) :
    ⊢ ownTracker (GF := GF) cfg tv t -∗
      ∃ p, ⌜t.peers !! i = some p⌝ ∗ ownProgress pr p ∗
        (ownProgress pr p -∗ ownTracker cfg tv t) := by
  iintro Hown
  icases ownTracker_lookup cfg tv t i pr Hpr $$ Hown with ⟨%p, %Hv, Hp, Hback⟩
  iexists p
  isplitr
  · ipureintro; exact Hv
  iframe Hp
  iintro Hp
  ihave Hown := Hback $$ %p Hp
  rw [GMap.insert_id t.peers i p Hv]
  iexact Hown

/-- The `Progress` records are indexed by the same peers as the map. -/
theorem ownTracker_prvals_dom (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTracker (GF := GF) cfg tv t -∗
      ⌜domSet t.peers = domSet t.prs⌝ ∗ ownTracker cfg tv t := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  isplitr
  · ipureintro
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom, GMap.elem_of_dom, ← Option.isSome_iff_exists,
      ← Option.isSome_iff_exists]
    exact (Hiff k).symm
  iapply ownTracker_intro cfg tv t.votes t.prs t.peers voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

/-- Read the progress map's points-to and domain out of the tracker without consuming
it (the map is read-only, hence persistent). -/
theorem ownTracker_progress_map (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTracker (GF := GF) cfg tv t -∗
      tv.Progress' ↦$□ t.prs ∗ ⌜domSet t.prs = cfg⌝ ∗ ownTracker cfg tv t := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  -- not `iframe Hprs`: it would also frame the copy inside the unsealed `ownTracker`,
  -- and `ownTracker_intro` would then no longer apply
  isplitr
  · iexact Hprs
  isplitr
  · ipureintro; exact Hprs_dom
  iapply ownTracker_intro cfg tv t.votes t.prs t.peers voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

/-- `trk.Progress[i]`, for a voter `i`: `becomeLeader` looks up `r.id`. Only voters
are in the map, whence the side condition. The `Progress` comes out as
`ownTracker_lookup` hands it out. -/
theorem wp_tracker_progress_lookup (tv : tracker.ProgressTracker) (t : Trk) (i : w64)
    (Hi : i ∈ cfg) :
    {{ ownTracker (GF := GF) cfg tv t }}
      (App (App (Val (map.lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty)))
        (Val #tv.Progress')) (Val #i))
    {{ (pr : Loc), RET #pr;
        ⌜t.prs !! i = some pr⌝ ∗
        ∃ p, ⌜t.peers !! i = some p⌝ ∗ ownProgress pr p ∗
          (∀ p', ownProgress pr p' -∗
                 ownTracker cfg tv ⟨t.votes, t.prs, <[i := p']> t.peers⟩) }} := by
  iintro %Φ Hown HΦ
  icases ownTracker_progress_map cfg tv t $$ Hown with ⟨#Hprs, %Hdom, Hown⟩
  obtain ⟨pr, Hpr⟩ : ∃ pr, t.prs !! i = some pr := by
    rw [← GMap.elem_of_dom, Hdom]; exact Hi
  wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ t.prs i _
    $$ Hprs with -
  rw [Hpr]
  simp only [Option.getD_some]
  iapply HΦ $$ %pr
  isplitr
  · ipureintro; rfl
  iapply ownTracker_lookup cfg tv t i pr Hpr $$ Hown

end proof2

/-! The Rocq tactics `progress_open`, `progress_abs_solve`, `trk_simpl`,
`progress_simpl` and `progress_abs_from` (opening `ownProgress`'s `%Habs` into the
record's fields, and closing `progressAbs pv i = some p` field by field) have Lean
counterparts in `(progressAbs_Some _ _ _).1 Habs` / `.2 ⟨…⟩` and `simp only` with the
`progress*` definitions; `progress_abs_solve` is the macro below. -/

/-- The pure side of `ownProgress_intro`: every field of the value against the
record. -/
macro "progress_abs_solve" : tactic =>
  `(tactic| (apply (Perennial.EtcdGrove.progressAbs_Some _ _ _).2;
             refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try rfl))

/-! ## A configuration, and changing to one

`ownConfig cfg cfgv prsm prs` is what `confchange.Restore` builds for a voters-only
configuration `cfg`: the `Config` value `cfgv` with its voter map, and the progress map
at `prsm` with its `Progress` objects. It is the part of `ownTracker` that
`switchToConfig` replaces; the vote tally and the tracker's other fields stay.
`ownTracker_reconfig` is the one place an `ownTracker` changes its `cfg` index. -/
section config
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

def ownConfig (cfg : GSet w64) (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) :
    IProp GF :=
  iprop(∃ (vref : Loc) (vm : GMap w64 Unit),
    "%Hcfgarr" ∷ ⌜cfgv.Voters'.arr = [vref, map.nil]⌝ ∗
    "%Hcfgl" ∷ ⌜cfgv.Learners' = map.nil⌝ ∗
    "%Hcfgln" ∷ ⌜cfgv.LearnersNext' = map.nil⌝ ∗
    "%Hcfgal" ∷ ⌜cfgv.AutoLeave' = false⌝ ∗
    "Hvref" ∷ vref ↦$ vm ∗
    "%Hvm" ∷ ⌜domSet vm = cfg⌝ ∗
    "#Hprsm" ∷ prsm ↦$□ prs ∗
    "%Hprs" ∷ ⌜domSet prs = cfg⌝ ∗
    "Hprogs" ∷ ([∗map] _k ↦ pr ∈ prs, ∃ p, ownProgress pr p) ∗
    "%Hcsz" ∷ ⌜(GMap.size cfg : Int) ≤ 2 ^ 62⌝)

/-- Name the values of a map's worth of objects: a `[∗map]` of existentials is a
`[∗map]` over two maps against some map of witnesses. -/
theorem bigSepM_exist_sepM2 {A B : Type} (m : GMap w64 A) (Φ : w64 → A → B → IProp GF) :
    ⊢ ([∗map] k ↦ x ∈ m, ∃ y, Φ k x y) -∗
      ∃ m' : GMap w64 B, [∗map] k ↦ x;y ∈ m;m', Φ k x y := by
  refine GMap.map_ind (P := fun m => ⊢ ([∗map] k ↦ x ∈ m, ∃ y, Φ k x y) -∗
      ∃ m' : GMap w64 B, [∗map] k ↦ x;y ∈ m;m', Φ k x y) ?_ ?_ m
  · iintro -
    iexists ∅
    iapply (BigSepM2.bigSepM2_empty _).2
    iempintro
  · intro k x m Hk IH
    iintro H
    icases (BigSepM.bigSepM_insert (Φ := fun k x => iprop(∃ y, Φ k x y)) (m := m) Hk).1 $$ H
      with ⟨⟨%y, Hy⟩, Hm⟩
    icases IH $$ Hm with ⟨%m', Hm⟩
    ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hm
    have Hk' : m' !! k = none := by
      cases h : m' !! k with
      | none => rfl
      | some _ =>
        have := (Hiff k).2 (by show (m' !! k).isSome = true; rw [h]; rfl)
        change (m !! k).isSome = true at this
        rw [Hk] at this; cases this
    iexists <[k := y]> m'
    iapply (BigSepM2.bigSepM2_insert (Φ := Φ) (m1 := m) (m2 := m') Hk Hk').2
    iframe Hy Hm

/-- The tracker `MakeProgressTracker` builds is an `ownTracker` over the empty
configuration. -/
theorem ownTracker_empty (tv : tracker.ProgressTracker) (v0 : Loc)
    (Harr : tv.Config'.Voters'.arr = [v0, map.nil])
    (Hl : tv.Config'.Learners' = map.nil)
    (Hln : tv.Config'.LearnersNext' = map.nil)
    (Hal : tv.Config'.AutoLeave' = false)
    (Hmi : 0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62) :
    ⊢ (v0 ↦$ (∅ : GMap w64 Unit) : IProp GF) -∗
      tv.Votes' ↦$ (∅ : GMap w64 Bool) -∗
      tv.Progress' ↦$□ (∅ : GMap w64 Loc) -∗
      ownTracker ∅ tv ⟨∅, ∅, ∅⟩ := by
  iintro Hv0 Hvotes #Hprs
  ihave Hl0 : ownIdsetOpt (GF := GF) tv.Config'.Learners' (∅ : GMap w64 Unit) $$ []
  · unfold ownIdsetOpt; ileft; ipureintro; exact ⟨Hl, rfl⟩
  ihave Hln0 : ownIdsetOpt (GF := GF) tv.Config'.LearnersNext' (∅ : GMap w64 Unit) $$ []
  · unfold ownIdsetOpt; ileft; ipureintro; exact ⟨Hln, rfl⟩
  ihave Hprogs : ([∗map] _k ↦ pr;p ∈ (∅ : GMap w64 Loc); (∅ : GMap w64 Progress),
      ownProgress (GF := GF) pr p) $$ []
  · iapply (BigSepM2.bigSepM2_empty _).2; iempintro
  iapply ownTracker_intro ∅ tv ∅ ∅ ∅ v0 ∅ ∅ ∅ GMap.dom_empty Harr Hal GMap.dom_empty
    ⟨rfl, rfl⟩ (by rw [GMap.size_empty]; decide) Hmi
    $$ Hvotes Hprs Hprogs Hv0 Hl0 Hln0

/-- Replace the configuration and the progress map of a tracker, keeping its tally and
inflight bound. The old configuration's voter map and `Progress` objects are dropped;
the new ones hold whatever `Restore` put in them. -/
theorem ownTracker_reconfig (cfg0 cfg : GSet w64) (tv : tracker.ProgressTracker) (t : Trk)
    (cfgv : tracker.Config) (prsm : Loc) (prs : GMap w64 Loc) :
    ⊢ ownTracker (GF := GF) cfg0 tv t -∗
      ownConfig cfg cfgv prsm prs -∗
      ∃ pvs, ownTracker cfg { tv with Config' := cfgv, Progress' := prsm }
               ⟨t.votes, prs, pvs⟩ := by
  iintro Hold Hnew
  iunfold ownTracker at Hold
  icases Hold with ⟨%voters_ref, %voters, %learners, %learnersNext, Hold⟩
  iNamed Hold
  iclear Hprs Hprogs Hvoters Hlearners HlearnersNext
  iunfold ownConfig at Hnew
  icases Hnew with ⟨%vref, %vm, Hnew⟩
  iNamed Hnew
  icases bigSepM_exist_sepM2 prs (fun _ pr (p : Progress) => ownProgress (GF := GF) pr p)
    $$ Hprogs with ⟨%pvs, Hprogs⟩
  iexists pvs
  ihave Hl0 : ownIdsetOpt (GF := GF) cfgv.Learners' (∅ : GMap w64 Unit) $$ []
  · unfold ownIdsetOpt; ileft; ipureintro; exact ⟨Hcfgl, rfl⟩
  ihave Hln0 : ownIdsetOpt (GF := GF) cfgv.LearnersNext' (∅ : GMap w64 Unit) $$ []
  · unfold ownIdsetOpt; ileft; ipureintro; exact ⟨Hcfgln, rfl⟩
  iapply ownTracker_intro cfg { tv with Config' := cfgv, Progress' := prsm } t.votes prs pvs
    vref vm ∅ ∅ Hprs Hcfgarr Hcfgal Hvm ⟨rfl, rfl⟩ Hcsz HmaxInfl
    $$ Hvotes Hprsm Hprogs Hvref Hl0 Hln0

end config

/-! ## Replication-side additions (2026-10-01)

Added for the log-replication tracker collections
(`Progress.MaybeUpdate`/`MaybeDecrTo`/`BecomeProbe`/`CanBumpCommit`,
`Inflights.FreeLE`, `ProgressTracker.Committed` and the quorum functions under it).
Kept at the end of the file, apart from the election-era definitions above, so that
concurrent edits merge.

(`w64Min`/`w64Max` moved to `Defs.lean` (2026-10-02), with the `Progress` methods that
use them.) -/

/-- Each voter's `Match`, read off the tracker's `Progress` values, with `0` for a peer
that has none (there is none such in `cfg`: `ownTracker`'s two maps have domain
`cfg`). `pvsAcked` is the `Option` form, which is what `matchAckIndexer.AckedIndex`
returns. -/
def pvsAcked (pvs : GMap w64 Progress) (v : w64) : Option w64 :=
  Progress.matched <$> pvs !! v

def pvsMatchAt (pvs : GMap w64 Progress) (v : w64) : w64 :=
  (pvsAcked pvs v).getD (W64 0)

/-- `N` is the quorum index of the per-voter values `f` over the voter set `s` -- what
`MajorityConfig.CommittedIndex` computes by sorting: `N` is one of the values, a quorum
of `s` has a value `≥ N`, and no larger index has a quorum. `IsQuorum` is
`Protocol/Model.lean`'s. -/
def IsQuorumIndex (s : GSet w64) (f : w64 → w64) (N : w64) : Prop :=
  (∃ v, v ∈ s ∧ f v = N) ∧
  IsQuorum s (GMap.filter (fun v _ => decide (uint.Z N ≤ uint.Z (f v))) s) ∧
  (∀ N' : w64, uint.Z N < uint.Z N' →
    ¬ IsQuorum s (GMap.filter (fun v _ => decide (uint.Z N' ≤ uint.Z (f v))) s))

section replication
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `min` on `uint64`; the framework has `wp_max2_uint64` but no `min`. -/
theorem wp_min2_uint64 (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.min [go.uint64, go.uint64])) (Val #x)) (Val #y))
    {{ RET #(w64Min x y); True }} := by
  wp_start
  wp_if_destruct
  · rw [show w64Min x y = x by unfold w64Min; simp_all]
    iapply HΦ; itrivial
  · rw [show w64Min x y = y by unfold w64Min; rw [ite_eq_right (by omega)]]
    iapply HΦ; itrivial

/-- The progress *map* with the `Progress` objects it points at -- the object a
`tracker.matchAckIndexer` is (a named `ProgressMap`), and exactly `ownTracker`'s
`Hprs` and `Hprogs` conjuncts. It is the precondition of
`matchAckIndexer.AckedIndex`, which receives the map and not the tracker:
`ProgressTracker.Committed` hands `matchAckIndexer(p.Progress)` to
`JointConfig.CommittedIndex`, which reads the voter map out of the *same* tracker while
the indexer is in use, so the indexer cannot be specified on `ownTracker` whole.

Indexed by the progresses only: the map's contents (the `*Progress` pointers) are
existential, since the one spec on it (`AckedIndex`) only carries them along; a caller
that knows them (`Committed`, from `ownTracker`) gets them back with
`progress_map_agree`. (Until 2026-10-08 the pointer map was an index.) -/
def ownProgressMap (m : Loc) (pvs : GMap w64 Progress) : IProp GF :=
  iprop(∃ (prs : GMap w64 Loc),
    "#Hprs" ∷ m ↦$□ prs ∗
    "Hprogs" ∷ ([∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress pr p))

/-- The `quorum.AckedIndexer` interface contract, against a resource `P` the
implementation needs and a function `acked` saying what each id's acknowledged index
is (`none`: "not a voter I know", which `MajorityConfig.CommittedIndex` counts as
`0`). Persistent, like `isStorage` (`InvStorage.lean`); one triple per method. -/
def isAckedIndexer (l : GoInterface) (P : IProp GF) (acked : w64 → Option w64) : IProp GF :=
  iprop(∃ (i : GoInterfaceOk),
    "%Hlok" ∷ ⌜l = interface.ok i⌝ ∗
    "#HAckedIndex" ∷ □ (∀ (id : w64),
       {{ P }}
         (App (Val #(methods i.ty go!"AckedIndex" i.v)) (Val #id))
       {{ RET (PairV #((acked id).getD (W64 0)) #((acked id).isSome)); P }}))

instance isAckedIndexer_pers (l : GoInterface) (P : IProp GF) (acked : w64 → Option w64) :
    Persistent (isAckedIndexer l P acked) := by
  unfold isAckedIndexer; infer_instance

end replication

end EtcdGrove
end Perennial

-- Projection lemmas, `@[simp, word_unfold]` (ProjSimps.lean).
proj_simps Perennial.EtcdGrove.inflightsRingOf Perennial.EtcdGrove.progressOf
