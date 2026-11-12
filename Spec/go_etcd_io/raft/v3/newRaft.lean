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
public import Proof.go_etcd_io.raft.v3.TracedBootVocab

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

-- (2026-11-02) `AttachRec` moved to `Proof.go_etcd_io.raft.v3.InvStorage`, `ConfStateOk` to
-- `Proof.go_etcd_io.raft.v3.InvRestore` (a spec file exposes only its `newRaft.spec`).

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
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
of a possibly non-empty storage as a premise, with an `InitialState` closure over `ownStorage`.) (2026-11-12, trace-check step 5, bootstrap positions 0-2) Both modes: the binders `γ` (the cluster's raft names: the trace mode `γ.reTrace`) and `vs` (the voters); `TraceLoggerOk cv.TraceLogger'` replaced by the capability's start (`trCapStart`, untraced that premise) and, traced, a fresh node (`BootFresh`); the `InitialState` answer also gives the storage's `trNoCut`, handed on; the post's ghost at the trace mode, `s.cq`, and the capability after the three lines (`bootAt vs cv.ID' 2`). -/
abbrev newRaft.spec : Prop :=
  ∀ (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (sn : StorNames) (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF) (cs' : CCState)
    (γ : RaftNames) (vs : List w64),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  LogIndicesOk σ.prev σ.ents → σ.pend = [] →
  uint.nat σ.prev.index' ≤ σ.fr → σ.fr ≤ uint.nat (committedAfter σ.prev hs) →
  uint.Z σ.fl ≤ uint.Z σ.prev.index' → σ.sg ≤ uint.nat σ.prev.index' →
  σ.dt = ∅ →
  uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64 →
  AttachRec sn σ.prev σ.ents (uint.nat (committedAfter σ.prev hs))
    (max (uint.nat σ.prev.index') (uint.nat cv.Applied')) →
  (HsEmpty hs ∨ uint.Z σ.prev.index' ≤ uint.Z hs.Commit' ∧
    uint.Z hs.Commit' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) →
  (cv.Applied' = W64 0 ∨ uint.Z σ.prev.index' ≤ uint.Z cv.Applied' ∧
    uint.Z cv.Applied' ≤ uint.Z (committedAfter σ.prev hs)) →
  restoreM csm.VotersOutgoing' csm.Voters' csm.Learners' csm.LearnersNext' csm.AutoLeave' =
    some cs' →
  (GMap.size (GMap.listToSet csm.Voters' ∪ GMap.listToSet csm.VotersOutgoing' ∪
    GMap.listToSet csm.Learners' ∪ GMap.listToSet csm.LearnersNext') : Int) ≤ 2 ^ 62 →
  ConfStateOk csm →
  -- (step 5) in place of `TraceLoggerOk cv.TraceLogger'` (now in `trCapStart`): a traced node is fresh
  (γ.reTrace ≠ none → BootFresh σ hs csm) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + 1)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + σ.ents.length)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn.unrec (interface.ok si) σ ∗
              -- (step 5) the storage's no-compaction, from the client's contract (traced)
              trNoCut γ.reTrace (interface.ok si) ∗ R' }}) ∗
      -- (step 5) the capability before the struct (untraced: the nil logger)
      trCapStart γ.reTrace γ cv.ID' cv.TraceLogger' (bootCfg vs) (bootPhase vs cv.ID') bootNone }}
    (App (Val #(functions newRaft [])) (Val #c))
  {{ (r : Loc) (s : NState) (cv' : Config), RET #r;
      R' ∗ ownRaftPhysC cs'.cfg r cv.ID' s ∗
      c ↦ cv' ∗ ⌜cv'.AsyncStorageWrites' = cv.AsyncStorageWrites'⌝ ∗
      ⌜NStateWf s ∧
        s.term = hs.Term' ∧
        s.vote = hs.Vote' ∧
        s.lead = W64 0 ∧ s.role = .follower ∧
        s.votes = ∅ ∧ s.outbox = [] ∧
        s.prevote = cv.PreVote' ∧
        -- (step 5) the check-quorum flag, for `rnTrace`
        s.cq = cv.CheckQuorum' ∧
        s.logst.prev = σ.prev ∧ s.logst.sents = σ.ents ∧ s.logst.uents = [] ∧
        s.logst.stored = σ.ents ∧
        s.logst.committed = committedAfter σ.prev hs ∧
        s.logst.applying = w64Max σ.prev.index'
          (if cv.Applied' = W64 0 then σ.prev.index' else cv.Applied') ∧
        s.logst.applied = s.logst.applying ∧
        s.logst.unpersisted = [] ∧ s.logst.snap = none ∧
        s.logst.storage = interface.ok si ∧
        s.logst.sn = sn ∧
        -- (step 5) the trace mode the cluster's (was `s.gh = { sn := sn }`)
        s.gh = { sn := sn, tr := γ.reTrace } ∧
        s.rd.states = [] ∧ s.rd.pend = [] ∧
        s.sdr = cv.StepDownOnRemoval' ∧ domSet s.progress = domSet cs'.prs ∧
        s.logst.dtk = uint.nat (committedAfter σ.prev hs)⌝ ∗
      -- (step 5) the storage's no-compaction, handed on, and the capability after positions 0-2
      trNoCut γ.reTrace (interface.ok si) ∗
      trCapB γ.reTrace γ r cv.ID' (bootCfg vs) false (bootPhase vs cv.ID') (bootAt vs cv.ID' 2) }}

end spec

end EtcdGrove
end Perennial
