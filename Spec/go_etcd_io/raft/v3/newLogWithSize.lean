/- Port of election_proof/spec_newLogWithSize.v (857d09190). -/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `newLogWithSize` builds the log over a `Storage`: everything is stable, the
unstable suffix is empty and starts at `LastIndex()+1` (where `offsetInProgress` starts
too: `ip` below), and `committed = applied = applying = FirstIndex()-1`, the compaction
boundary.

**Over the start bundle** (U8 v2 step 4, 2026-10-29; 2026-11-01, durability stage I-6: from a
storage holding a log from the base `b` to `last`, until then a fresh one). `newLogWithSize` reads
`FirstIndex` and `LastIndex` before `newRaft` calls `InitialState`, and a `MemoryStorage`'s
contract (`isStorage`) can only be made after `InitialState` returns (it reads the stored snapshot
without the lock: issues/raft-memorystorage-initialstate-unlocked.md). So the storage is not
`isStorageD sn st ∗ ownStorage sn st σ` here but a client frame `R` with two persistent triples:
over `R`, `FirstIndex` answers `b + 1` and `LastIndex` `last`. The post gives `R` back, with the
wand that completes the log at a view `σ` of the storage from the base `b` to `last` (contiguous
indices, nothing pending; the floor at most the base, frozen from the base to at most the commit (2026-11-02, stage II (o): `restartStorage`'s freeze point; until then only at the base), no snapshot handed
out past it, no term certified past it) once raft's view of the storage is supplied: `newRaft`
makes it after `InitialState`. (Until 2026-11-01 the fresh view `{ prev := ⟨0, 0⟩, ents := [],
pend := [] }` only; until 2026-10-29 a general view's `isStorageD` and `ownStorage` as premises,
`06420c24b1^`.)

**Why a wand.** `ownRaftLog l ls` holds the storage's resources inside it (at the struct's
`storage` field: `LogState` has no field the client could read them back from), and the client
needs `R` again for `InitialState`; so the post hands out `R` together with the wand that
completes the log once raft's view is given.

**The struct out, and the log at a loaded state** (2026-11-01, durability stage I-6, the attach
record). On a restart the storage key's attach record (`StorNames.a0`/`c0`/`ct`: the applied bound
`max σ.b A`, the stored commit, its terms) is ahead of the struct `newLogWithSize` builds
(`committed = applied = applying = b`), and raft's view catches up with it (`storCaught`, in
`ownStorage`) only once `newRaft` has run `loadState` and `appliedTo`. Between `InitialState` and
`appliedTo` there is no `ownRaftLog`: the client may already compact up to the record, which the
view's triples (`isStorageD`) do not allow below the floor. So the post gives the struct `l ↦ lv0`
itself (its fields as built: nothing unstable, the counters at `b`) and the wand completes the log
at the state the caller's `loadState`/`appliedTo` moved the struct to (`committed := c`, `applied =
applying := a`), raft's view at the base with the floor at most `a` and the terms certified at most
`c` (of the view's log at or above the base). (Until 2026-11-01 the wand completed the log at `b`.)

The `Logger` is a non-nil one with `isLogger` (since 2026-10-01): `ownRaftLog` carries
it, for the `Infof`s of `findConflict` and `unstable.truncateAndAppend`, and the struct
literal installs it as both `l.logger` and `l.unstable.logger`. -/
abbrev newLogWithSize.spec : Prop :=
  ∀ (si : GoInterfaceOk) (lg : Logger) (maxSize : w64)
    (sn : StorNames) (lok : GoInterfaceOk) (R : IProp GF) (b last : Nat),
  lg = interface.ok lok →
  -- a positive applying-size limit (2026-10-05): the log starts with applying unpaused
  -- at size `0`, and `nextCommittedEnts` `Panicf`s on
  -- `maxApplyingEntsSize - applyingEntsSize <= 0`
  0 < uint.Z maxSize →
  -- (durability stage I-6) the stored log's bounds
  b ≤ last → (last : Int) + 1 < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ R ∗
      -- the start bundle's reads
      ({{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
        {{ RET (PairV #(W64 (b + 1)) #interface.nil); R }}) ∗
      ({{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
        {{ RET (PairV #(W64 last) #interface.nil); R }}) ∗
      isLogger lok }}
    (App (App (App (Val #(functions newLogWithSize [])) (Val #(interface.ok si))) (Val #lg))
      (Val #maxSize))
  {{ (l : Loc) (ip : w64), RET #l;
      R ∗ ⌜uint.Z ip = (last : Int) + 1⌝ ∗
      -- (durability stage I-6) the struct as built
      ∃ lv0 : raftLog, l ↦ lv0 ∗
      ⌜lv0.storage' = interface.ok si ∧ lv0.committed' = W64 b ∧ lv0.applied' = W64 b ∧
        lv0.applying' = W64 b ∧ lv0.unstable'.snapshot' = null ∧ lv0.unstable'.entries'.len = W64 0 ∧
        lv0.unstable'.offset' = ip ∧ lv0.unstable'.offsetInProgress' = ip ∧
        lv0.unstable'.snapshotInProgress' = false ∧ lv0.applyingEntsSize' = W64 0 ∧
        lv0.applyingEntsPaused' = false ∧ lv0.maxApplyingEntsSize' = maxSize⌝ ∗
      -- the log, at the counters `loadState`/`appliedTo` set, over raft's view from the base
      (∀ (σ : StorState) (c a : w64),
        ⌜uint.nat σ.prev.index' = b ∧ b + σ.ents.length = last ∧ LogIndicesOk σ.prev σ.ents ∧
          σ.pend = [] ∧ b ≤ σ.fr ∧ σ.fr ≤ uint.nat c ∧ σ.sg ≤ b ∧
          b ≤ uint.nat a ∧ uint.nat a ≤ uint.nat c ∧ uint.nat c ≤ last ∧ uint.nat σ.fl ≤ uint.nat a ∧
          (∀ k t, σ.dt !! k = some t → k ≤ uint.nat c ∧
            (b ≤ k → termAt σ.prev σ.ents (W64 (k : Int)) = some t))⌝ -∗
       l ↦ { lv0 with committed' := c, applied' := a, applying' := a } -∗
       isStorageD sn (interface.ok si) -∗
       ownStorage sn (interface.ok si) σ -∗
       ownRaftLog l
         { prev := σ.prev, sents := σ.ents, uents := [], committed := c,
           applied := a, snap := none, inprogress := ip,
           applying := a, unpersisted := [], stored := σ.ents, apsize := W64 0,
           apmax := maxSize, storage := interface.ok si, ksn := [], sn := sn, fl := σ.fl,
           sg := σ.sg, dtk := uint.nat c }) }}

end spec

end EtcdGrove
end Perennial
