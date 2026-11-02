/- Port of election_proof/spec_newRaft.v (857d09190).

# `newRaft`: the constructor of `ownRaftPhys`

This triple is the witness that `ownRaftPhys` is **satisfiable** by a struct the Go code
actually builds: from a `Config` and a `Storage` it produces `ownRaftPhys cfg r id s` at
a well-formed follower state. Every other spec in the development takes `ownRaftPhys`
as given; this is the one that establishes it.

## What it assumes, and why

`newRaft` panics on several inputs, and its spec has to exclude each one. The premises
are, in order:

- `ConfigValid cv` (`Spec/Config__validate.lean`): what `validate` checks, so
  `validate` returns `nil` -- plus a non-nil `Logger`.
- **`MaxInflightMsgs < 2^62`: not implied by `validate`**, which only checks `> 0`.
  `ownTracker`'s `HmaxInfl` (`InvTracker.lean`) demands it because `Inflights.grow`
  computes `len(buffer) * 2`, which overflows a Go `int` once the buffer reaches
  `2^62`. So `ownRaftPhys` is **unsatisfiable for a valid `Config` with
  `MaxInflightMsgs ≥ 2^62`** (found writing this spec, 2026-09-24). Not a bug a real run
  can hit -- the buffer only grows to `2^62` with that many messages in flight -- but a
  gap between what raft accepts and what the proof covers.
- the development's scope: `DisableProposalForwarding =
  false` (a follower forwards proposals; since 2026-10-02, for `stepFollower`'s
  forwarding arm). `PreVote` is either value since 2026-10-04: the state records it
  (`NState.prevote`); so is `CheckQuorum` since 2026-10-17 (`NState.cq`; until then it was
  required `false`).
- the storage's contents (`ownStorage (interface.ok si) prev ents ss`): contiguous
  indices, and a snapshot `ss` that is empty or the compaction boundary (since
  2026-10-03; `Spec/newLogWithSize.lean` says why). (Until 2026-10-13 also no
  configuration-change entry, `HnoConfChange`'s scope assumption, false of a node
  `RawNode.Bootstrap` just bootstrapped.)
- `Storage.InitialState` returns `(hs, cs, nil)` and lends `cs.Voters` (whatever the
  storage's snapshot index `ss'` is by then: the log built by `newLogWithSize` does not
  expose it). This is a
  premise, not a clause of `isStorageD`: it is a fact about one storage at one moment,
  and nothing else calls the method.
- `hs.Commit` lies in `[prev.index, lastIndex]` unless `hs` is empty (else `loadState`
  panics), and `Applied` is `0` or lies in `[prev.index, committed]` (else `appliedTo`
  panics).
- the `ConfState` is **voters-only**, with a list of **distinct, non-zero** voters. Each
  clause is needed: learners/joint configurations are out of scope; `Restore` skips a zero
  id and de-duplicates, after which `assertConfStatesEquivalent` panics. (Until 2026-10-16,
  stage R8b, also non-empty: an empty voter set is what a new cluster's node starts with,
  etcd's `StartNode`, and `confchange.Restore` then returns the empty tracker's own maps
  (`Restore.spec_empty`), which `switchToConfig` installs; the result is `ownRaftPhys ∅`,
  which `RawNode.Bootstrap` moves to the peers. A node joining an existing cluster with no
  peers stays there until it receives a snapshot, out of scope.)
- **at most `2^62` voters.** The tracker sorts the voter ids with `slices.Sort`, whose
  heapsort fallback overflows `int` past `2^62` elements (`ownTracker`'s `Hcfg_size`).

## What it gives

`ownRaftPhys` over the voter set, at a state that is `NStateWf` (ready for `Step`), a
follower with no leader, an empty tally and an empty outbox, whose `term` and `vote` are
the persisted `HardState`'s. For a fresh storage (`hs` empty) that is
`NStateRel s initPState` (`newRaft_post_init`, Rocq `election.v`): the struct `newRaft`
builds refines the protocol state `ownRaftGhost_alloc` starts every node in.

Lean notes: the `InitialState` premise's `WP` is applied to the value
`#(methods si.ty go!"InitialState" si.v)`, as in `isStorageD`; Rocq's
`Φ (#hs, #cs, #interface.nil)%V` is `Φ (PairV (PairV #hs #cs) #interface.nil)`.
`HsEmpty` gets a `Decidable` instance so that `committedAfter` can branch on it
(Rocq's `bool_decide`).

raft v3.7 (2026-10-15, stage R4): `Storage.InitialState` returns two pointers `(hp, cs)`: the hard
state, possibly `nil` (`hsOpt hp hs`, read-only; `IsEmptyHardState` and `loadState` read it), and
the conf state, read-only for good (`csPts cs □ csm al`, its `AutoLeave` cell set or not: D7's
`MemoryStorage.InitialState` gives it set, `al = true`; a `Storage` that returns
`&pb.ConfState{Voters: …}` gives it `nil`, `al = false`; `newRaft` reads it through `ownCSM`,
`csPts_weaken`, so it asks for neither -- 2026-10-16, stage R6b, the register's storage; until
then `csPts cs □ csm true`), beside `ownStorage` given back at once.
`newRaft` reads the conf state (`confchange.Restore`, `assertConfStatesEquivalent`) while the log
it built holds the storage, so the conf state cannot be lent with a wand back to the storage
(phase 2's statement, which `MemoryStorage` could not meet: its `InitialState` returns the
storage's own conf-state pointer). The conf state is the record `csm : ConfStateM` (until the retarget the
Goose value `cs` and the list `voters` its `Voters` slice held, lent at `dqv`): the voters are
`csm.Voters'`, the scope voters-only as before (`csm`'s other lists empty, `AutoLeave` off), and the
tracked ids `GMap.listToSet csm.Voters'`.
-/
module

public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Spec.go_etcd_io.raft.v3.Config__validate
public import Proof.go_etcd_io.raft.v3.InvRestore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts]

-- (2026-10-26, raft's signature, stage 1) `HsEmpty` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

instance HsEmpty.decidable (hs : HardStateM) : Decidable (HsEmpty hs) := by
  unfold HsEmpty; infer_instance

/-- `raftLog.committed` after `newRaft`'s `loadState` (skipped for an empty
`HardState`). -/
def committedAfter (prev : entryID) (hs : HardStateM) : w64 :=
  if HsEmpty hs then prev.index' else hs.Commit'

/-- (2026-11-01, durability stage I-6) **The storage names `sn` carry the attach record of a
storage holding the log `prev :: ents`**, with the commit `c0` and the applied bound `a0` raft
restores: what `restartStorage`'s continuation hands out (`nodeAppliedLb γ K a0`, `nodeCommitLb γ
K c0`), recorded in the key (`storKeyNames`). Every recorded term is the log's at its index, from
the base up to `c0`: so raft's view, once its commit reaches `c0`, certifies them (`storCaught`). -/
def AttachRec (sn : StorNames) (prev : entryID) (ents : List EntryM) (c0 a0 : Nat) : Prop :=
  sn.a0 = a0 ∧ sn.c0 = c0 ∧
  ∀ (i : Nat) (t : w64), (i, t) ∈ sn.ct → i ≤ c0 →
    uint.nat prev.index' ≤ i ∧ termAt prev ents (W64 (i : Int)) = some t

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `newRaft(c)`: see the file header. (2026-11-01, durability stage I-6, the attach record: the
storage names carry it (`AttachRec`: the applied bound `max b A`, the commit `loadState` restores,
the terms on the way), the `InitialState` continuation makes raft's view at the base without it
(`ownStorage sn.unrec`: the client may compact up to the record from the attach on, before raft
has caught up), and `newRaft` catches up (`storCaught`, certifying the recorded terms: the
certification bound at the restored commit) before it returns the node. 2026-11-01, durability
stage I-6: from a storage holding a log from the base `b` to `last`, the hard state `hs` restored (`loadState`) and `Applied` within
the committed part (`appliedTo`); the `ConfState` any that `Restore` accepts (`restoreM`), joint
or with learners; raft's view `σ` of the storage at the base. Until then a fresh storage, an empty
hard state, nothing applied, voters only.) (raft-final phase 1, 2026-10-29: U8 v2 step 4's boot bundle,
decision (B), `notes/u8v2/step4-boot-newLogWithSize.patch`) Over a fresh storage: a frame `R` with
`FirstIndex` answering `1` and `LastIndex` `0` over it (`newLogWithSize` reads them before
`InitialState`), and `InitialState` answering the hard state and conf state, after which the caller
makes raft's view of the storage (`isStorageD sn ∗ ownStorage sn σ`, `σ` fresh) and gets back its
frame `R'`; the API's `bootStorage` is this at the contract `isStorage γ id`. (Until then raft's view
of a possibly non-empty storage as a premise, with an `InitialState` closure over `ownStorage`.) -/
abbrev newRaft.spec : Prop :=
  ∀ (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (sn : StorNames) (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF) (cs' : CCState),
  -- the Config
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  -- `ReadOnlySafe` (2026-10-12): lease-based reads need bounded clock drift
  cv.ReadOnlyOption' = W64 0 →
  -- conf-change validation on (2026-10-13)
  cv.DisableConfChangeValidation' = false →
  -- a positive applying-size limit (2026-10-05)
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  -- (durability stage I-6) the storage's view raft makes: from the base (contiguous indices,
  -- nothing pending, frozen from the base up to at most the restored commit, the floor, the snapshot handed out and the terms
  -- certified at most the base), within 64 bits
  LogIndicesOk σ.prev σ.ents → σ.pend = [] →
  -- (2026-11-02, stage II (o): `restartStorage`'s freeze point) frozen up to at most the commit
  -- `loadState` restores
  uint.nat σ.prev.index' ≤ σ.fr → σ.fr ≤ uint.nat (committedAfter σ.prev hs) →
  uint.Z σ.fl ≤ uint.Z σ.prev.index' → σ.sg ≤ uint.nat σ.prev.index' →
  -- (2026-11-02, stage II (o)) the terms certified at most the base, the base's its term
  (∀ k t, σ.dt !! k = some t → k ≤ uint.nat σ.prev.index' ∧
    (uint.nat σ.prev.index' ≤ k → termAt σ.prev σ.ents (W64 (k : Int)) = some t)) →
  uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64 →
  -- (2026-11-01, durability stage I-6) the storage key's attach record (`restartStorage`'s
  -- continuation): the applied bound `max b A`, the commit `loadState` restores, the view's terms
  -- at the recorded indices (from the base)
  AttachRec sn σ.prev σ.ents (uint.nat (committedAfter σ.prev hs))
    (max (uint.nat σ.prev.index') (uint.nat cv.Applied')) →
  -- `loadState`'s bound (it panics otherwise), unless the hard state is empty
  (HsEmpty hs ∨ uint.Z σ.prev.index' ≤ uint.Z hs.Commit' ∧
    uint.Z hs.Commit' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) →
  -- `appliedTo`'s (it panics otherwise): `Applied` `0` or within `[prev.index, committed]`
  (cv.Applied' = W64 0 ∨ uint.Z σ.prev.index' ≤ uint.Z cv.Applied' ∧
    uint.Z cv.Applied' ≤ uint.Z (committedAfter σ.prev hs)) →
  -- the persisted ConfState: one `Restore` accepts, at the tracker's state `cs'`
  restoreM csm.VotersOutgoing' csm.Voters' csm.Learners' csm.LearnersNext' csm.AutoLeave' =
    some cs' →
  csm.Voters'.length + csm.VotersOutgoing'.length + csm.Learners'.length +
    csm.LearnersNext'.length ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      -- (raft-final phase 1) the start bundle (`restartStorage`'s shape; durability stage I-6: at
      -- the view's base and last index)
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + 1)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + σ.ents.length)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn.unrec (interface.ok si) σ ∗
              R' }}) }}
    (App (Val #(functions newRaft [])) (Val #c))
  {{ (r : Loc) (s : NState) (cv' : Config), RET #r;
      R' ∗ ownRaftPhysC cs'.cfg r cv.ID' s ∗
      -- the `Config`, `validate`d (2026-10-09): `NewRawNode` reads it after
      c ↦ cv' ∗ ⌜cv'.AsyncStorageWrites' = cv.AsyncStorageWrites'⌝ ∗
      ⌜NStateWf s ∧
        s.term = hs.Term' ∧
        s.vote = hs.Vote' ∧
        s.lead = W64 0 ∧ s.role = .follower ∧
        s.votes = ∅ ∧ s.outbox = [] ∧
        s.prevote = cv.PreVote' ∧
        -- the log, as the storage and the `HardState` give it (2026-10-09, for
        -- `NewRawNode`): the stored entries, nothing unstable, the commit index the
        -- `HardState` restores, applying from `Config.Applied`, nothing handed out
        s.logst.prev = σ.prev ∧ s.logst.sents = σ.ents ∧ s.logst.uents = [] ∧
        s.logst.stored = σ.ents ∧
        s.logst.committed = committedAfter σ.prev hs ∧
        s.logst.applying = w64Max σ.prev.index'
          (if cv.Applied' = W64 0 then σ.prev.index' else cv.Applied') ∧
        -- (2026-11-02, stage II (o), for `rawNodeAt`) `appliedTo` moves both
        s.logst.applied = s.logst.applying ∧
        s.logst.unpersisted = [] ∧ s.logst.snap = none ∧
        -- the storage it reads (2026-10-10, for `RNState.storage`)
        s.logst.storage = interface.ok si ∧
        -- (U8 v2) and its names
        s.logst.sn = sn ∧
        -- no ghost lower bound yet (2026-10-10, `NGhost`); (U8 v2) the storage names mirrored
        s.gh = { sn := sn } ∧
        -- no read state (2026-10-13)
        s.rd.states = [] ∧ s.rd.pend = [] ∧
        -- (2026-10-14, reconfiguration stage B7 part 2, for a dynamic `NewRawNode`) the
        -- `Config`'s `StepDownOnRemoval`, and the voters tracked, no learner
        s.sdr = cv.StepDownOnRemoval' ∧ domSet s.progress = domSet cs'.prs ∧
        -- (raft-final phase 2; durability stage I-6: raft certified the attach record's terms,
        -- up to the commit `loadState` restored) the certification bound (for `SdtTie` at
        -- `RestartNode`)
        s.logst.dtk = uint.nat (committedAfter σ.prev hs)⌝ }}

end spec

end EtcdGrove
end Perennial
