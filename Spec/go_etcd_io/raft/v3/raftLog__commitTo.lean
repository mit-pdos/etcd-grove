/-
Port of election_proof/spec_raftLog__commitTo.v (feb5c73d4).

Lean notes:
* The reference `raftLog__commitToⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:930` is to the
  Lean generated code `raftLog.commitTo.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog
public import Proof.go_etcd_io.raft.v3.Plog

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

/-- `l.commitTo(leaderTerm, tocommit)` (raft#139): raise `committed` to
`min(tocommit, lastIndex())`, never lower it, but only for a leader of the log's
`leaderTerm` -- `logCommitTo` (`InvRaftlog.lean`).

The body (`raftLog.commitTo.impl`, `Code/go_etcd_io/raft/v3.lean`):

    if leaderTerm != l.leaderTerm { return }
    tocommit = min(tocommit, l.lastIndex())
    if tocommit > l.committed { l.committed = tocommit }

No premise: the `Panicf` on `tocommit > lastIndex()` is gone, the commit index is cut at
the last index instead. Until raft#139 the spec was (`git show lean:` this file)

    uint.Z tocommit ≤ plogLastIndexZ ls.prev (ls.sents ++ ls.uents) →
    {{ ownRaftLog l ls }} l.commitTo(tocommit)
    {{ ownRaftLog l { ls with committed := plogCommitTo ls.committed tocommit } }}

and the new one gives that post exactly when `leaderTerm = ls.leaderTerm` under the old
premise (`logCommitTo_at_term`); at another term it leaves `committed` alone. -/
abbrev raftLog.commitTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (lt tocommit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"commitTo")) (Val #lt))
      (Val #tocommit))
  {{ RET #();
      ownRaftLog l { ls with committed := logCommitTo ls lt tocommit } }}

end spec

end EtcdGrove
end Perennial
