/- Port of election_proof/spec_raftLog__firstIndex.v (feb5c73d4). -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvReadylog

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

/-- `l.firstIndex()`: one past the compaction boundary.

The log comes back at the same state `ls`, because `raftLog.term` calls this on itself
and needs the entry list to come back unchanged -- see `ownRaftLog` in
`InvRaftlog.lean`.

The function ends in a `panic` on an error from `Storage`. `Logger.wp_logf`
deliberately does not cover the panicking methods, so this proof has to *reach* the
`Storage` call with its precondition satisfied; that is the whole content of the
lemma.

(D19i part 1, 2026-10-18) The application may have compacted the storage, up to the floor raft
published (`LogState.fl`): the answer is at least one past the log's boundary, at most one past
the floor, and above the log's only once the storage is compacted (`storCut`). -/
abbrev raftLog.firstIndex.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"firstIndex")) (Val #()))
  {{ (i : w64), RET #i;
      ownRaftLog l ls ∗
      ⌜uint.Z ls.prev.index' + 1 ≤ uint.Z i ∧
        uint.Z i ≤ max (uint.Z ls.prev.index') (uint.Z ls.fl) + 1⌝ ∗
      (⌜uint.Z i = uint.Z ls.prev.index' + 1⌝ ∨ storCut ls.storage (uint.Z i - 1)) }}

end spec

end EtcdGrove
end Perennial
