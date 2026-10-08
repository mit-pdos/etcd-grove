/- Port of election_proof/spec_matchAckIndexer__AckedIndex.v (feb5c73d4).

Lean notes: Rocq's `default (W64 0) x` is `x.getD (W64 0)`, and
`bool_decide (is_Some x)` is `x.isSome` (the form `isAckedIndexer`'s contract uses).
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `l.AckedIndex(id)` for `l : matchAckIndexer`, the progress map seen as a
`quorum.AckedIndexer` (`tracker.matchAckIndexer.AckedIndex.impl`,
`EtcdRaft/Code/go_etcd_io/raft/v3/tracker.lean`; tracker.go:169):

    pr, ok := l[id]
    if !ok { return 0, false }                    // exit 1
    return quorum.Index(pr.Match), true           // exit 2

No panic, no call. The receiver is the map itself (`matchAckIndexer` is a named
`map[uint64]*Progress`), so the triple is stated on `ownProgressMap`
(`InvTracker.lean`) -- the progress map with the `Progress` objects it points at -- not
on the tracker: see that definition for why. The result is `pvsAcked pvs id` in the
`(value-or-0, ok)` form of `isAckedIndexer`'s contract, which is what this triple
exists to discharge. -/
abbrev tracker.matchAckIndexer.AckedIndex.spec : Prop :=
  ∀ (mref : Loc) (pvs : GMap w64 Progress) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      ownProgressMap mref pvs }}
    (App (Val (mref @!! tracker.matchAckIndexer.ty @!! go!"AckedIndex")) (Val #id))
  {{ RET (PairV #((pvsAcked pvs id).getD (W64 0)) #((pvsAcked pvs id).isSome));
      ownProgressMap mref pvs }}

end spec

end EtcdGrove
end Perennial
