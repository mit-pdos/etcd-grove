/- Port of election_proof/spec_newLogWithSize.v (857d09190). -/
import EtcdGrove.Raft.InvRaftPhys

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
unstable suffix is empty and starts at `LastIndex()+1`, and
`committed = applied = FirstIndex()-1`, the compaction boundary.

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

**The postcondition is `ownRaftLog_unfold`'s right-hand side, not `ownRaftLog`**, plus
`lv.storage' = st`. `ownRaftLog l ls` forgets which `Storage` interface value the log
holds: `LogState` has no storage field, so `ownStorage` sits inside it at
`lv.storage'` for an `lv` nobody outside can name. `newRaft` calls
`c.Storage.InitialState()` *after* building the log -- through the `Config`'s copy of
the same interface value -- and needs the log's `ownStorage` for that call; without
`lv.storage' = st` the two are unrelated and the call cannot be proved. The caller
folds the result into
`ownRaftLog l ⟨prev, ents, [], prev.index', prev.index', none, ip, prev.index', [], …⟩`
with `ownRaftLog_unfold`. The principled fix is a `storage` field in `LogState`
(notes/STATUS.md).

The `Logger` is a non-nil one with `isLogger` (since 2026-10-01): `ownRaftLogCore`
carries it, for the `Infof`s of `findConflict` and `unstable.truncateAndAppend`, and the
struct literal installs it as both `l.logger` and `l.unstable.logger`. -/
abbrev newLogWithSize.spec : Prop :=
  ∀ (st : Storage) (lg : Logger) (maxSize : w64)
    (prev : entryID) (ents : List raftpb.Entry) (ss : entryID) (lok : GoInterfaceOk),
  LogIndicesOk prev ents →
  (∀ e ∈ ents, e.Type' = EntryNormal) →
  (uint.Z ss.index' = 0 ∨ ss = prev) →
  lg = interface.ok lok →
  -- a positive applying-size limit (2026-10-05): the log starts with applying unpaused
  -- at size `0`, and `nextCommittedEnts` `Panicf`s on
  -- `maxApplyingEntsSize - applyingEntsSize <= 0`
  0 < uint.Z maxSize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isStorage st ∗
      ownStorage st prev ents ss ∗ isLogger lok }}
    (App (App (App (Val #(functions newLogWithSize [])) (Val #st)) (Val #lg))
      (Val #maxSize))
  {{ (l : Loc) (lv : raftLog), RET #l;
      l ↦ lv ∗
      ⌜lv.storage' = st ∧
        lv.committed' = prev.index' ∧
        lv.applied' = prev.index' ∧
        lv.applying' = prev.index' ∧
        uint.Z lv.unstable'.offsetInProgress'
          = uint.Z prev.index' + (ents.length : Int) + 1 ∧
        lv.applyingEntsSize' = W64 0 ∧
        lv.maxApplyingEntsSize' = maxSize⌝ ∗
      ownRaftLogCore lv none prev ents [] [] }}

end spec

end EtcdGrove
end Perennial
