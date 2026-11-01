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

**A fresh boot, over the boot bundle** (U8 v2 step 4, 2026-10-29). `newLogWithSize` reads
`FirstIndex` and `LastIndex` before `newRaft` calls `InitialState`, and a `MemoryStorage`'s
contract (`isStorage`) can only be made after `InitialState` returns (it reads the stored snapshot
without the lock: issues/raft-memorystorage-initialstate-unlocked.md). So the storage is not
`isStorageD sn st ∗ ownStorage sn st σ` here but a client frame `R` with two persistent triples:
over `R`, `FirstIndex` answers `1` and `LastIndex` `0` (a fresh storage: nothing compacted, no
entry). The post gives `R` back, with the wand that completes the log at the fresh view
`{ prev := ⟨0, 0⟩, ents := [], pend := [] }` (no floor raised, frozen only at the compaction
point, no snapshot handed out, no term certified) once raft's view of the storage is supplied:
`newRaft` makes it after `InitialState`. (Until then the premises were a general view `σ` --
contiguous indices `LogIndicesOk`, nothing pending, fresh to raft -- with the view's read triples
`isStorageD sn st` and `ownStorage sn st σ`, which the post lent back with the wand.)

**Why a wand.** `ownRaftLog l ls` holds the storage's resources inside it (at the struct's
`storage` field: `LogState` has no field the client could read them back from), and the client
needs `R` again for `InitialState`; so the post hands out `R` together with the wand that
completes the log once raft's view is given.

The `Logger` is a non-nil one with `isLogger` (since 2026-10-01): `ownRaftLog` carries
it, for the `Infof`s of `findConflict` and `unstable.truncateAndAppend`, and the struct
literal installs it as both `l.logger` and `l.unstable.logger`. -/
abbrev newLogWithSize.spec : Prop :=
  ∀ (si : GoInterfaceOk) (lg : Logger) (maxSize : w64)
    (sn : StorNames) (lok : GoInterfaceOk) (R : IProp GF),
  lg = interface.ok lok →
  -- a positive applying-size limit (2026-10-05): the log starts with applying unpaused
  -- at size `0`, and `nextCommittedEnts` `Panicf`s on
  -- `maxApplyingEntsSize - applyingEntsSize <= 0`
  0 < uint.Z maxSize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ R ∗
      -- the boot bundle's reads: a fresh storage
      ({{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
        {{ RET (PairV #(W64 1) #interface.nil); R }}) ∗
      ({{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
        {{ RET (PairV #(W64 0) #interface.nil); R }}) ∗
      isLogger lok }}
    (App (App (App (Val #(functions newLogWithSize [])) (Val #(interface.ok si))) (Val #lg))
      (Val #maxSize))
  {{ (l : Loc) (ip : w64), RET #l;
      R ∗ ⌜uint.Z ip = 1⌝ ∗
      (isStorageD sn (interface.ok si) -∗
       ownStorage sn (interface.ok si)
         ({ prev := entryID.mk (W64 0) (W64 0), ents := [], pend := [] } : StorState) -∗
       ownRaftLog l
         { prev := entryID.mk (W64 0) (W64 0), sents := [], uents := [], committed := W64 0,
           applied := W64 0, snap := none, inprogress := ip,
           applying := W64 0, unpersisted := [], stored := [], apsize := W64 0,
           apmax := maxSize, storage := interface.ok si, ksn := [], sn := sn }) }}

end spec

end EtcdGrove
end Perennial
