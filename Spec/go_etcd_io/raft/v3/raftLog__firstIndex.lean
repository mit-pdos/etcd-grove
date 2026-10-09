/- Port of election_proof/spec_raftLog__firstIndex.v (feb5c73d4). -/
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

/-- `l.firstIndex()`: one past the compaction boundary.

The log comes back at the same state `ls`, because `raftLog.term` calls this on itself
and needs the entry list to come back unchanged -- see `ownRaftLog` in
`InvRaftlog.lean`.

The function ends in a `panic` on an error from `Storage`. `Logger.wp_logf`
deliberately does not cover the panicking methods, so this proof has to *reach* the
`Storage` call with its precondition satisfied; that is the whole content of the
lemma. -/
abbrev raftLog.firstIndex.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"firstIndex")) (Val #()))
  {{ (i : w64), RET #i;
      ownRaftLog l ls ∗
      ⌜uint.Z i = uint.Z ls.prev.index' + 1⌝ }}

end spec

end EtcdGrove
end Perennial
