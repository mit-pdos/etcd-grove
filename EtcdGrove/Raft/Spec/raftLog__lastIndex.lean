/- Port of election_proof/spec_raftLog__lastIndex.v (feb5c73d4). -/
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

/-- `l.lastIndex()`: the index of the last entry.

Stated at the log's state `ls`, and the postcondition pins the value:
`prev.index + |sents| + |uents|`. That equation is what `term`'s and `lastEntryID`'s
proofs need in order to satisfy `Storage.Term`'s range premise.

Both branches (the `unstable` one and the `storage` fallback) have to agree, which is
what the `unstable.offset` conjunct of `ownRaftLog` buys. Like `firstIndex`, the
`Panicf` path has to be shown unreachable rather than assumed away. -/
abbrev raftLog.lastIndex.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"lastIndex")) (Val #()))
  {{ (i : w64), RET #i;
      ownRaftLog l ls ∗
      ⌜uint.Z i = uint.Z ls.prev.index' + (ls.sents.length : Int)
                  + (ls.uents.length : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
