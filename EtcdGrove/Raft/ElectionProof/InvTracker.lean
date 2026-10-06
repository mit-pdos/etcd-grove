/-
Port of `election_proof/inv_tracker.v`: the progress tracker and per-peer progress.

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
-/
import EtcdGrove.Raft.ElectionProof.Defs

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

/-! ### Inflights

A sliding window of in-flight append sizes. Election never inspects it: `reset`
allocates a fresh one per peer, and `maybeSendAppend` only asks whether it is full. So
the contents are existential -- what matters is that the object and its buffer are
owned, so that a `Progress` can be overwritten wholesale. -/

/-- `Full()`'s answer, read off the `Inflights` value (`Inflights.Full.impl`,
`Perennial/Code/go_etcd_io/raft/v3/tracker.lean`):

    in.count == in.size || (in.maxBytes != 0 && in.bytes >= in.maxBytes)

It is a function of `iv` and not an existential because `Inflights.Add` **panics**
when it is `true` ("cannot add into a Full inflights"), so `Add`'s triple can only be
stated -- truthfully -- at an `Inflights` value the caller knows is not full. That is
why `ownInflights` is indexed by the value. -/
def inflightsFull (iv : tracker.Inflights) : Bool :=
  decide (iv.count' = iv.size') ||
    (decide (iv.maxBytes' ≠ W64 0) && decide (uint.Z iv.maxBytes' ≤ uint.Z iv.bytes'))

/-- The ring-buffer invariant, over the `Inflights` value and the *length* of the
buffer it points at.

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
def InflightsOk (iv : tracker.Inflights) (buflen : Int) : Prop :=
  0 ≤ sint.Z iv.start' ∧
  (0 ≤ sint.Z iv.count' ∧ sint.Z iv.count' ≤ sint.Z iv.size') ∧
  (0 ≤ buflen ∧ buflen ≤ sint.Z iv.size') ∧
  sint.Z iv.size' < 2 ^ 62 ∧
  (sint.Z iv.start' < sint.Z iv.size' ∨ (sint.Z iv.size' = 0 ∧ sint.Z iv.start' = 0)) ∧
  (sint.Z iv.start' + sint.Z iv.count' ≤ buflen ∨ buflen = sint.Z iv.size')

/-- The one predicate for an `Inflights` object, indexed by its value `iv` and the
contents `buf` of its ring buffer. `buf` is in the index because `grow` is specified
by what it does to the buffer. A caller that does not care writes
`∃ iv buf, ownInflights l iv buf`. (Until 2026-09-23 there were two forms,
`own_inflights_at l iv` and the existential `own_inflights l`, and `grow`/`reset`
were stated on raw points-tos; main's notes/decisions.md, "Three layers".) -/
def ownInflights (l : Loc) (iv : tracker.Inflights) (buf : List tracker.inflight) :
    IProp GF :=
  iprop("Hiv" ∷ l ↦ iv ∗
    "Hbuf" ∷ iv.buffer' ↦* buf ∗
    "Hbuf_cap" ∷ ownSliceCap tracker.inflight iv.buffer' (DFrac.own 1) ∗
    "%Hinfl_ok" ∷ ⌜InflightsOk iv (buf.length : Int)⌝)

/-! ### Per-peer replication progress

Ownership is of the whole `Progress` *value*, because `reset`'s `Visit` closure
overwrites one wholesale (`pr <-[tracker.Progress] CompositeLiteral ...`); a predicate
over selected fields could not justify that write. What hangs off the value is its
`Inflights` object.

A field assignment like `becomeLeader`'s `pr.RecentActive := true` steps through
`pr ↦ pv` with the generated `AccessStrict` instances and leaves `Inflights'` alone,
so `ownInflights` survives it untouched. -/

/-- The three states a `Progress` may legally be in
(`StateProbe`/`StateReplicate`/`StateSnapshot` = `W64 0`/`1`/`2`, in
`Perennial/Code/go_etcd_io/raft/v3/tracker.lean`). `Progress.IsPaused` **panics** on
anything else ("unexpected state"), and `bcastAppend` reaches it on every peer, so this
has to be an invariant rather than a hope. It is: `reset`'s `Visit` closure writes a
literal with no `State` field, i.e. the zero value `StateProbe`, and `ResetState` --
the only other writer on this path, behind `BecomeReplicate` and `BecomeSnapshot` --
is always passed one of the three. -/
def ProgressStateOk (st : tracker.StateType) : Prop :=
  st = W64 0 ∨ st = W64 1 ∨ st = W64 2

/-- The one predicate for a `Progress` object, indexed by its value `pv` and its
`Inflights` value `iv`: `IsPaused`'s answer is a function of `State` and
`MsgAppFlowPaused`, and `SentEntries` reaches `Inflights.Add`, whose precondition is
`inflightsFull iv = false`. The ring buffer's contents are not in the index: no
`Progress` method looks at them. A caller that does not care writes
`∃ pv iv, ownProgress pr pv iv`. (Until 2026-09-23 this was `own_progress_at`, beside
an existential `own_progress pr`.) -/
def ownProgress (pr : Loc) (pv : tracker.Progress) (iv : tracker.Inflights) : IProp GF :=
  iprop("Hpv" ∷ pr ↦ pv ∗
    "Hinfl" ∷ (∃ buf, ownInflights pv.Inflights' iv buf) ∗
    -- No learners are in scope, so no voter's `Progress` is a learner's. Added
    -- 2026-09-16 because `raft.wp_promotable` needs it: `promotable` returns
    -- `pr != nil && !pr.IsLearner && ...`, and without this conjunct its
    -- postcondition `b = decide (id ∈ cfg)` is not derivable. It is preserved by
    -- everything that writes a `Progress`: `reset`'s `Visit` closure copies
    -- `IsLearner` across, and `BecomeReplicate` / `RecentActive := true` do not
    -- touch it.
    "%Hnolearner" ∷ ⌜pv.IsLearner' = false⌝ ∗
    "%Hstate_ok" ∷ ⌜ProgressStateOk pv.State'⌝)

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
`ownTracker cfg tv votes` therefore owns exactly what the tracker *value* `tv` points
at: the vote map, the progress map together with the `Progress` objects in it, and the
id sets of the configuration. `votes` is the recorded vote tally.

The configuration is *simple*, not joint -- no reconfiguration and no learners are in
scope -- which is recorded the same way `readonly.lean` records it: the `JointConfig`
array is `[voters_ref, map.nil]`. The voter set and the domain of the progress map are
both `cfg`.

`pvs` is what each `Progress` holds, with its `Inflights` value, by peer
(`NState.prvals`): `prs` and `pvs` are paired key by key, so they have the same
domain. (Until 2026-09-29 the values were existential inside, and a caller that needed
one across a call it made with the struct sealed had to take the tracker out of
`ownRaftPhys` on loan.) -/
def ownTracker (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)) :
    IProp GF :=
  iprop(∃ (voters_ref : Loc) (voters : GMap w64 Unit)
    (learners learnersNext : GMap w64 Unit),
  "Hvotes" ∷ tv.Votes' ↦$ votes ∗
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
  "#Hprs" ∷ tv.Progress' ↦$□ prs ∗
  "Hprogs" ∷ ([∗map] _k ↦ pr;v ∈ prs;pvs, ownProgress pr v.1 v.2) ∗
  "%Hprs_dom" ∷ ⌜domSet prs = cfg⌝ ∗
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
  -- `0 ≤ sint.Z cap`. Nothing else bounds the voter set: no Iris ownership constrains
  -- the cardinality of a `GSet w64`, so `size cfg = 2^64` is consistent with every
  -- other conjunct here. This is a property of the configuration, so it belongs with
  -- the configuration.
  "%Hcfg_size" ∷ ⌜(GMap.size cfg : Int) < 2 ^ 63⌝ ∗
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
  -- until 2026-09-24; main's notes/false-statements.md) -- and `newRaft` copies it into
  -- the tracker, so the `< 2^62` half is an extra premise of `newRaft`'s spec, not
  -- something raft checks. So this predicate excludes valid configs with
  -- `MaxInflightMsgs ≥ 2^62`. Needed because `reset`'s `Visit` closure calls
  -- `tracker.NewInflights(r.trk.MaxInflight, …)`, and the ring-buffer invariant of
  -- `ownInflights` pins `0 ≤ size < 2^62` (see `InflightsOk`). Like `Hcfg_size` it is
  -- a property of the configuration and is never written on the election path. Added
  -- 2026-09-20 for `bcastAppend`.
  "%HmaxInfl" ∷ ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝)

/-- Re-sealing a tracker a proof has taken apart, as one `iapply`. (In Rocq,
`iExists …; iFrame "∗#%"` against the unfolded predicate cost ~30s per use in a proof
body; main's notes/gotchas.md.) The pure premises are in the order the conjuncts
appear in `ownTracker`. -/
theorem ownTracker_intro (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights))
    (voters_ref : Loc) (voters learners learnersNext : GMap w64 Unit)
    (Hprs_dom : domSet prs = cfg)
    (Hvoters_arr : tv.Config'.Voters'.arr = [voters_ref, map.nil])
    (Hautoleave : tv.Config'.AutoLeave' = false)
    (Hvoters_dom : domSet voters = cfg)
    (Hno_learners : learners = ∅ ∧ learnersNext = ∅)
    (Hcfg_size : (GMap.size cfg : Int) < 2 ^ 63)
    (HmaxInfl : 0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62) :
    ⊢ (tv.Votes' ↦$ votes : IProp GF) -∗
      tv.Progress' ↦$□ prs -∗
      ([∗map] _k ↦ pr;v ∈ prs;pvs, ownProgress pr v.1 v.2) -∗
      voters_ref ↦$ voters -∗
      ownIdsetOpt tv.Config'.Learners' learners -∗
      ownIdsetOpt tv.Config'.LearnersNext' learnersNext -∗
      ownTracker cfg tv votes prs pvs := by
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
from `ElectionProof/Protocol.lean` (and so is `elem_of_granted`). -/

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
at different times, so lending resolves it. See `spec_ProgressTracker__Visit.v` (main)
for how this was got wrong. -/
def visitClosure (trk : Loc) (votes : GMap w64 Bool) (prs : GMap w64 Loc) (f : GoFunc)
    (I : IProp GF) : IProp GF :=
  iprop(∀ (i : w64) (pr : Loc) (tv : tracker.ProgressTracker)
      (pvs : GMap w64 (tracker.Progress × tracker.Inflights))
      (pv : tracker.Progress) (iv : tracker.Inflights),
    {{ ⌜i ∈ cfg⌝ ∗ ⌜prs !! i = some pr⌝ ∗ ⌜pvs !! i = some (pv, iv)⌝ ∗
        ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗
        trk ↦ tv ∗ ownProgress pr pv iv ∗
        (∀ pv' iv', ownProgress pr pv' iv' -∗
                    ownTracker cfg tv votes prs (<[i := (pv', iv')]> pvs)) ∗ I }}
      (App (App (Val #f) (Val #i)) (Val #pr))
    {{ RET #(); ∃ tv' pvs', trk ↦ tv' ∗ ownTracker cfg tv' votes prs pvs' ∗ I }})

/-- The inflight-window bound, read out without consuming the tracker. `reset`'s
`Visit` closure calls `tracker.NewInflights(r.trk.MaxInflight, ...)`, whose premise
this is; the closure cannot reach `ownTracker` itself, so `reset` pulls the fact into
the Lean context before the `Visit`. -/
theorem ownTracker_maxinflight (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)) :
    ⊢ ownTracker (GF := GF) cfg tv votes prs pvs -∗
      ⌜0 ≤ sint.Z tv.MaxInflight' ∧ sint.Z tv.MaxInflight' < 2 ^ 62⌝ ∗
      ownTracker cfg tv votes prs pvs := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  isplitr
  · ipureintro; exact HmaxInfl
  iapply ownTracker_intro cfg tv votes prs pvs voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

/-- Borrow one voter's `Progress` out of the tracker, by its key in the progress map
the tracker is indexed by, at the value `pvs` records for it; give it back at any
value, which the index then records. The caller can come back to the *same* pointer,
and the same value, after any call that returns the tracker at the same `prs` and
`pvs`. -/
theorem ownTracker_lookup (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights))
    (i : w64) (pr : Loc) (Hpr : prs !! i = some pr) :
    ⊢ ownTracker (GF := GF) cfg tv votes prs pvs -∗
      ∃ pv iv, ⌜pvs !! i = some (pv, iv)⌝ ∗ ownProgress pr pv iv ∗
        (∀ pv' iv', ownProgress pr pv' iv' -∗
                    ownTracker cfg tv votes prs (<[i := (pv', iv')]> pvs)) := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  obtain ⟨⟨pv, iv⟩, Hv⟩ := Option.isSome_iff_exists.1 ((Hiff i).1 (by show (prs !! i).isSome = true; rw [Hpr]; rfl))
  icases BigSepM2.bigSepM2_insert_acc (Φ := fun _ pr v => ownProgress (GF := GF) pr v.1 v.2)
    (m1 := prs) (m2 := pvs) Hpr Hv $$ Hprogs with ⟨Hp, Hback⟩
  iexists pv, iv
  isplitr
  · ipureintro; exact Hv
  iframe Hp
  iintro %pv' %iv' Hp
  ihave Hprogs := Hback $$ %pr %(pv', iv') Hp
  have Hins : (Iris.Std.PartialMap.insert prs i pr : GMap w64 Loc) = prs := GMap.insert_id prs i pr Hpr
  rw [Hins]
  iapply ownTracker_intro cfg tv votes prs _ voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

/-- The same, given back at the value it was borrowed at. -/
theorem ownTracker_lookup_same (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights))
    (i : w64) (pr : Loc) (Hpr : prs !! i = some pr) :
    ⊢ ownTracker (GF := GF) cfg tv votes prs pvs -∗
      ∃ pv iv, ⌜pvs !! i = some (pv, iv)⌝ ∗ ownProgress pr pv iv ∗
        (ownProgress pr pv iv -∗ ownTracker cfg tv votes prs pvs) := by
  iintro Hown
  icases ownTracker_lookup cfg tv votes prs pvs i pr Hpr $$ Hown
    with ⟨%pv, %iv, %Hv, Hp, Hback⟩
  iexists pv, iv
  isplitr
  · ipureintro; exact Hv
  iframe Hp
  iintro Hp
  ihave Hown := Hback $$ %pv %iv Hp
  rw [GMap.insert_id pvs i (pv, iv) Hv]
  iexact Hown

/-- The `Progress` values are indexed by the same peers as the map. -/
theorem ownTracker_prvals_dom (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)) :
    ⊢ ownTracker (GF := GF) cfg tv votes prs pvs -∗
      ⌜domSet pvs = domSet prs⌝ ∗ ownTracker cfg tv votes prs pvs := by
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
  iapply ownTracker_intro cfg tv votes prs pvs voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

/-- Read the progress map's points-to and domain out of the tracker without consuming
it (the map is read-only, hence persistent). -/
theorem ownTracker_progress_map (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)) :
    ⊢ ownTracker (GF := GF) cfg tv votes prs pvs -∗
      tv.Progress' ↦$□ prs ∗ ⌜domSet prs = cfg⌝ ∗ ownTracker cfg tv votes prs pvs := by
  iintro Hown
  iunfold ownTracker at Hown
  icases Hown with ⟨%voters_ref, %voters, %learners, %learnersNext, Hown⟩
  iNamed Hown
  isplitr
  · iexact Hprs
  isplitr
  · ipureintro; exact Hprs_dom
  iapply ownTracker_intro cfg tv votes prs pvs voters_ref voters learners learnersNext
    Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size HmaxInfl
    $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

/-- `trk.Progress[i]`, for a voter `i`: `becomeLeader` looks up `r.id`. Only voters
are in the map, whence the side condition. The `Progress` comes out as
`ownTracker_lookup` hands it out. -/
theorem wp_tracker_progress_lookup (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights))
    (i : w64) (Hi : i ∈ cfg) :
    {{ ownTracker (GF := GF) cfg tv votes prs pvs }}
      (App (App (Val (map.lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty)))
        (Val #tv.Progress')) (Val #i))
    {{ (pr : Loc), RET #pr;
        ⌜prs !! i = some pr⌝ ∗
        ∃ pv iv, ⌜pvs !! i = some (pv, iv)⌝ ∗ ownProgress pr pv iv ∗
          (∀ pv' iv', ownProgress pr pv' iv' -∗
                      ownTracker cfg tv votes prs (<[i := (pv', iv')]> pvs)) }} := by
  iintro %Φ Hown HΦ
  icases ownTracker_progress_map cfg tv votes prs pvs $$ Hown with ⟨#Hprs, %Hdom, Hown⟩
  obtain ⟨pr, Hpr⟩ : ∃ pr, prs !! i = some pr := by
    rw [← GMap.elem_of_dom, Hdom]; exact Hi
  wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ prs i _
    $$ Hprs with -
  rw [Hpr]
  simp only [Option.getD_some]
  iapply HΦ $$ %pr
  isplitr
  · ipureintro; rfl
  iapply ownTracker_lookup cfg tv votes prs pvs i pr Hpr $$ Hown

end proof2

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
    "Hprogs" ∷ ([∗map] _k ↦ pr ∈ prs, ∃ pv iv, ownProgress pr pv iv) ∗
    "%Hcsz" ∷ ⌜(GMap.size cfg : Int) < 2 ^ 63⌝)

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
      ownTracker ∅ tv ∅ ∅ ∅ := by
  iintro Hv0 Hvotes #Hprs
  ihave Hl0 : ownIdsetOpt (GF := GF) tv.Config'.Learners' (∅ : GMap w64 Unit) $$ []
  · unfold ownIdsetOpt; ileft; ipureintro; exact ⟨Hl, rfl⟩
  ihave Hln0 : ownIdsetOpt (GF := GF) tv.Config'.LearnersNext' (∅ : GMap w64 Unit) $$ []
  · unfold ownIdsetOpt; ileft; ipureintro; exact ⟨Hln, rfl⟩
  ihave Hprogs : ([∗map] _k ↦ pr;v ∈ (∅ : GMap w64 Loc);
      (∅ : GMap w64 (tracker.Progress × tracker.Inflights)), ownProgress (GF := GF) pr v.1 v.2)
      $$ []
  · iapply (BigSepM2.bigSepM2_empty _).2; iempintro
  iapply ownTracker_intro ∅ tv ∅ ∅ ∅ v0 ∅ ∅ ∅ GMap.dom_empty Harr Hal GMap.dom_empty
    ⟨rfl, rfl⟩ (by rw [GMap.size_empty]; decide) Hmi
    $$ Hvotes Hprs Hprogs Hv0 Hl0 Hln0

/-- Replace the configuration and the progress map of a tracker, keeping its tally and
inflight bound. The old configuration's voter map and `Progress` objects are dropped;
the new ones hold whatever `Restore` put in them. -/
theorem ownTracker_reconfig (cfg0 cfg : GSet w64) (tv : tracker.ProgressTracker)
    (votes : GMap w64 Bool) (prs0 : GMap w64 Loc)
    (pvs0 : GMap w64 (tracker.Progress × tracker.Inflights)) (cfgv : tracker.Config)
    (prsm : Loc) (prs : GMap w64 Loc) :
    ⊢ ownTracker (GF := GF) cfg0 tv votes prs0 pvs0 -∗
      ownConfig cfg cfgv prsm prs -∗
      ∃ pvs, ownTracker cfg { tv with Config' := cfgv, Progress' := prsm } votes prs pvs := by
  iintro Hold Hnew
  iunfold ownTracker at Hold
  icases Hold with ⟨%voters_ref, %voters, %learners, %learnersNext, Hold⟩
  iNamed Hold
  iclear Hprs Hprogs Hvoters Hlearners HlearnersNext
  iunfold ownConfig at Hnew
  icases Hnew with ⟨%vref, %vm, Hnew⟩
  iNamed Hnew
  ihave Hprogs := BigSepM.bigSepM_mono
    (Ψ := fun _ pr => iprop(∃ v : tracker.Progress × tracker.Inflights,
      ownProgress (GF := GF) pr v.1 v.2))
    (fun _ => by iintro ⟨%pv, %iv, Hp⟩; iexists (pv, iv); iexact Hp) $$ Hprogs
  icases bigSepM_exist_sepM2 prs
    (fun _ pr (v : tracker.Progress × tracker.Inflights) => ownProgress (GF := GF) pr v.1 v.2)
    $$ Hprogs with ⟨%pvs, Hprogs⟩
  iexists pvs
  ihave Hl0 : ownIdsetOpt (GF := GF) cfgv.Learners' (∅ : GMap w64 Unit) $$ []
  · unfold ownIdsetOpt; ileft; ipureintro; exact ⟨Hcfgl, rfl⟩
  ihave Hln0 : ownIdsetOpt (GF := GF) cfgv.LearnersNext' (∅ : GMap w64 Unit) $$ []
  · unfold ownIdsetOpt; ileft; ipureintro; exact ⟨Hcfgln, rfl⟩
  iapply ownTracker_intro cfg { tv with Config' := cfgv, Progress' := prsm } votes prs pvs
    vref vm ∅ ∅ Hprs Hcfgarr Hcfgal Hvm ⟨rfl, rfl⟩ Hcsz HmaxInfl
    $$ Hvotes Hprsm Hprogs Hvref Hl0 Hln0

end config

end EtcdGrove
end Perennial
