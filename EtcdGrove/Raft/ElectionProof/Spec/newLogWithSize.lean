/-
Port of `election_proof/spec_newLogWithSize.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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

**The postcondition is `ownRaftLog_unfold`'s right-hand side, not `ownRaftLog`**, plus
`lv.storage' = st`. `ownRaftLog l ls` forgets which `Storage` interface value the log
holds: `LogState` has no storage field, so `ownStorage` sits inside it at
`lv.storage'` for an `lv` nobody outside can name. `newRaft` calls
`c.Storage.InitialState()` *after* building the log -- through the `Config`'s copy of
the same interface value -- and needs the log's `ownStorage` for that call; without
`lv.storage' = st` the two are unrelated and the call cannot be proved. The caller
folds the result into `ownRaftLog l ⟨prev, ents, [], prev.index', prev.index'⟩` with
`ownRaftLog_unfold`. The principled fix is a `storage` field in `LogState`
(notes/STATUS.md). -/
abbrev newLogWithSize.spec : Prop :=
  ∀ (st : Storage) (lg : Logger) (maxSize : w64)
    (prev : entryID) (ents : List raftpb.Entry),
  LogIndicesOk prev ents →
  (∀ e ∈ ents, e.Type' = EntryNormal) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isStorage st ∗
      ownStorage st prev ents }}
    (App (App (App (Val #(functions newLogWithSize [])) (Val #st)) (Val #lg))
      (Val #maxSize))
  {{ (l : Loc) (lv : raftLog), RET #l;
      l ↦ lv ∗
      ⌜lv.storage' = st ∧
        lv.committed' = prev.index' ∧
        lv.applied' = prev.index'⌝ ∗
      ownRaftLogCore lv prev ents [] }}

end spec

end EtcdGrove
end Perennial
