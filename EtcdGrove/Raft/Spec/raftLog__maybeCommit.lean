/- Port of election_proof/spec_raftLog__maybeCommit.v (feb5c73d4).

Lean notes: `bool_decide` is `decide`.
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

/-- `l.maybeCommit(at)`: commit up to `at.index` if `at` is a non-zero-term entry of
our log past the commit index.

The body (`raftLog.maybeCommit.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3.lean`):

    if at.term != 0 && at.index > l.committed && l.matchTerm(at) {
        l.commitTo(at.index); return true
    }
    return false

The result `b` is exactly the guard, and the log moves to `committed := at.index` when
it is `true`. `commitTo`'s premise (`at.index <= lastIndex()`) is not a premise here:
`matchTerm` put `at.index` inside the log (`plogTermAt_some_range`), so its `Panicf` is
dead with no help from the caller. The leader's `raft.maybeCommit` calls this with
`at = (trk.Committed(), r.Term)`. -/
abbrev raftLog.maybeCommit.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (aid : entryID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"maybeCommit")) (Val #aid))
  {{ (b : Bool), RET #b;
      ownRaftLog l (if b then { ls with committed := aid.index' } else ls) ∗
      ⌜b = decide (aid.term' ≠ W64 0 ∧
                   uint.Z ls.committed < uint.Z aid.index' ∧
                   PlogMatches ls.prev (ls.sents ++ ls.uents) aid)⌝ }}

end spec

end EtcdGrove
end Perennial
