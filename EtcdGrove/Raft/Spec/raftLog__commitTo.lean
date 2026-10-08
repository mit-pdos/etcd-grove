/-
Port of election_proof/spec_raftLog__commitTo.v (feb5c73d4).

Lean notes:
* The reference `raftLog__commitToⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:930` is to the
  Lean generated code `raftLog.commitTo.impl`.
-/
import EtcdGrove.Raft.InvRaftPhys
import EtcdGrove.Raft.Plog

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

/-- `l.commitTo(tocommit)`: raise `committed` to `tocommit`, never lower it --
`plogCommitTo` (`Plog.lean`).

The body (`raftLog.commitTo.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3.lean`):

    if l.committed < tocommit {
        if l.lastIndex() < tocommit { l.logger.Panicf(...) }
        l.committed = tocommit
    }

The premise `tocommit <= lastIndex()` is exactly what makes the `Panicf` dead; it is the
protocol fact of the design's table ("Protocol facts the code needs": a leader's commit
index in an accepted `MsgApp`/`MsgHeartbeat` is within the follower's log), and for
`maybeCommit` it follows from `matchTerm`. It also keeps `ownRaftLog`'s `Hcommitted`
true at the new value. -/
abbrev raftLog.commitTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (tocommit : w64),
  uint.Z tocommit ≤ plogLastIndexZ ls.prev (ls.sents ++ ls.uents) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"commitTo")) (Val #tocommit))
  {{ RET #();
      ownRaftLog l { ls with committed := plogCommitTo ls.committed tocommit } }}

end spec

end EtcdGrove
end Perennial
