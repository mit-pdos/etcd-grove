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

/-- `l.commitTo(tocommit)`: raise `committed` to `tocommit`, never lower it --
`plogCommitTo` (`Plog.lean`).

The body (`raftLog.commitTo.impl`, `Code/go_etcd_io/raft/v3.lean`):

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

/-- etcd-io/raft#104 (head `d9c4b358`, `notes/pr-verify/raft-104.md`): the out-of-range
case no longer `Panicf`s; it `Warningf`s and sets `committed` to `lastIndex()`:

    if l.committed < tocommit {
        if l.lastIndex() < tocommit {
            l.logger.Warningf(...); l.committed = l.lastIndex(); return
        }
        l.committed = tocommit
    }

So there is no premise, and `committed` becomes `max(committed, min(tocommit,
lastIndex()))` (`committed ≤ lastIndex()` is `ownRaftLog`'s `Hcommitted`, so in the
clamped case it is `lastIndex()`). Under the old premise this is `plogCommitTo committed
tocommit`: `raftLog.commitTo.spec_implies_old` (`Proof/.../raftLog__commitTo.lean`).
What the statement does not say, and cannot at this level, is whether the entries up to
`lastIndex()` it marks committed are the cluster's committed entries: that is the
protocol's business, and in the protocol the proof models the clamped case is
unreachable (`heartbeat_commit_le_last`). -/
abbrev raftLog.commitTo.specNew : Prop :=
  ∀ (l : Loc) (ls : LogState) (tocommit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"commitTo")) (Val #tocommit))
  {{ (c : w64), RET #();
      ownRaftLog l { ls with committed := c } ∗
      ⌜uint.Z c = max (uint.Z ls.committed)
          (min (uint.Z tocommit) (plogLastIndexZ ls.prev (ls.sents ++ ls.uents)))⌝ }}

end spec

end EtcdGrove
end Perennial
