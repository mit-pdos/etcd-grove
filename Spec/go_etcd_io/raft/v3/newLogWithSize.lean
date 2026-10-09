/- Port of election_proof/spec_newLogWithSize.v (857d09190). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `newLogWithSize` builds the log over a `Storage`: everything is stable, the
unstable suffix is empty and starts at `LastIndex()+1` (where `offsetInProgress` starts
too: `ip` below), and `committed = applied = applying = FirstIndex()-1`, the compaction
boundary.

Two premises are about the storage's *contents* and are not in `isStorage`: that the
stored entries carry contiguous indices after `prev` (`LogIndicesOk`), and that none is
a configuration change. The first is true of any correct `Storage` (and of
`MemoryStorage`) but `ownStorage` is abstract, so a client has to supply it. The second
is the development's no-reconfiguration scope (`HnoConfChange`, `InvRaftlog.lean`) and
is **false of a freshly bootstrapped etcd node**, whose storage holds the
`EntryConfChange`s `Bootstrap` wrote (notes/STATUS.md, "What still needs fixing").

A third (2026-10-03) is about the storage's snapshot `ss`: it is empty
(`ss.index' = 0`) or it *is* the compaction boundary (`ss = prev`). That is
`ownRaftLog`'s `StoredSnapOk` at `committed = prev.index'`, the commit index the log
starts at. It holds of a fresh `MemoryStorage` (no snapshot, dummy entry `0`) and of the
restart path `ApplySnapshot`-then-`Append` (which sets `ents[0]` to the snapshot's id);
it excludes restarting on a storage whose snapshot lies above its first index, whose
index raft would only learn is committed from the `HardState` `loadState` reads after
this call.

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
    (σ : StorState) (lok : GoInterfaceOk),
  LogIndicesOk σ.prev σ.ents →
  (∀ e ∈ σ.ents, e.Type' = EntryNormal) →
  (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  lg = interface.ok lok →
  -- a positive applying-size limit (2026-10-05): the log starts with applying unpaused
  -- at size `0`, and `nextCommittedEnts` `Panicf`s on
  -- `maxApplyingEntsSize - applyingEntsSize <= 0`
  0 < uint.Z maxSize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isStorage st ∗
      ownStorage st σ ∗ isLogger lok }}
    (App (App (App (Val #(functions newLogWithSize [])) (Val #st)) (Val #lg))
      (Val #maxSize))
  {{ (l : Loc) (ip : w64), RET #l;
      ⌜uint.Z ip = uint.Z σ.prev.index' + (σ.ents.length : Int) + 1⌝ ∗
      ownStorage st σ ∗
      (ownStorage st σ -∗
       ownRaftLog l
         { prev := σ.prev, sents := σ.ents, uents := [], committed := σ.prev.index',
           applied := σ.prev.index', snap := none, inprogress := ip,
           applying := σ.prev.index', unpersisted := [], apsize := W64 0,
           apmax := maxSize }) }}

end spec

end EtcdGrove
end Perennial
