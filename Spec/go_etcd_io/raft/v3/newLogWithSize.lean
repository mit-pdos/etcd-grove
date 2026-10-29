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

One premise is about the storage's *contents* and is not in `isStorage`: that the
stored entries carry contiguous indices after `prev` (`LogIndicesOk`), true of any
correct `Storage` (and of `MemoryStorage`) but `ownStorage` is abstract, so a client has
to supply it. (Until 2026-10-13 a second: that none is a configuration change, the
no-reconfiguration scope `HnoConfChange`, false of a freshly bootstrapped etcd node,
whose storage holds the `EntryConfChange`s `Bootstrap` wrote.)

(U8 v2, 2026-10-29) The storage is raft's view `σ` of it (`ownStorage sn st σ`, its ranges
from the compaction point, the end and the authorities of raft's ghost names `sn`), frozen only at
the compaction point, no floor raised and no snapshot handed out yet; and the read triples of the
view (`isStorage sn st`, derived from the contract, `isStorage_of_V`). Until U8 v2 the storage's
snapshot was premised to be empty or at the boundary (`StoredSnapOk`) and certified
(`initKsnCert`); the stored snapshot is now the client's.

**The postcondition lends the storage back.** `newRaft` calls
`c.Storage.InitialState()` *after* building the log -- through the `Config`'s copy of
the same interface value `st` -- and needs the storage's `ownStorage` for that call.
`ownRaftLog l ls` cannot provide it: `LogState` has no storage field, so the log's
`ownStorage` sits inside it at the struct's `storage` field, a value nobody outside can
relate to `st`. So the post hands out `ownStorage st σ` together with the wand that
completes the log at the initial state once it is given back. (Until 2026-10-09 the post
was `l ↦ lv`, the facts about `lv`'s fields with `lv.storage' = st`, and the internal
`ownRaftLogCore lv none σ.prev σ.ents [] []`, which `newRaft` folded into `ownRaftLog`;
the principled fix would be a `storage` field in `LogState`, notes/STATUS.md.)

The `Logger` is a non-nil one with `isLogger` (since 2026-10-01): `ownRaftLog` carries
it, for the `Infof`s of `findConflict` and `unstable.truncateAndAppend`, and the struct
literal installs it as both `l.logger` and `l.unstable.logger`. -/
abbrev newLogWithSize.spec : Prop :=
  ∀ (st : Storage) (lg : Logger) (maxSize : w64)
    (sn : StorNames) (σ : StorState) (lok : GoInterfaceOk),
  LogIndicesOk σ.prev σ.ents →
  -- nothing pending (2026-10-10)
  σ.pend = [] →
  lg = interface.ok lok →
  -- a positive applying-size limit (2026-10-05): the log starts with applying unpaused
  -- at size `0`, and `nextCommittedEnts` `Panicf`s on
  -- `maxApplyingEntsSize - applyingEntsSize <= 0`
  0 < uint.Z maxSize →
  -- (D19i part 1) the floor not raised yet: the storage's view, fresh to raft
  σ.fl = W64 0 →
  -- (U8 v2) frozen only at the compaction point, no snapshot handed out
  σ.fr = uint.nat σ.prev.index' → σ.sg = 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isStorage sn st ∗
      ownStorage sn st σ ∗ isLogger lok }}
    (App (App (App (Val #(functions newLogWithSize [])) (Val #st)) (Val #lg))
      (Val #maxSize))
  {{ (l : Loc) (ip : w64), RET #l;
      ⌜uint.Z ip = uint.Z σ.prev.index' + (σ.ents.length : Int) + 1⌝ ∗
      ownStorage sn st σ ∗
      (ownStorage sn st σ -∗
       ownRaftLog l
         { prev := σ.prev, sents := σ.ents, uents := [], committed := σ.prev.index',
           applied := σ.prev.index', snap := none, inprogress := ip,
           applying := σ.prev.index', unpersisted := [], stored := σ.ents, apsize := W64 0,
           apmax := maxSize, storage := st, ksn := [], sn := sn }) }}

end spec

end EtcdGrove
end Perennial
