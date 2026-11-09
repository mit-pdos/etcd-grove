/-
## `matchAckIndexer.AckedIndex(id)` (internal)

**Users.** `Committed`'s `CommittedIndex`, through the `AckedIndexer` interface (the contract
`Quorum.isAckedIndexer` with `P = progressMapOwn`). Mirrors the code: a lookup and `pr.Match`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.tracker.Assumptions]

/-- (internal) The peer's match index, if tracked. -/
def matchAckIndexer.AckedIndex.spec : Prop :=
  ∀ (mp : GoMap) (prs : GMap w64 Loc) (pv : GMap w64 ProgressV) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressMapOwn mp prs pv }}
    (App (Val (mp @!! go_etcd_io.raft.v3.tracker.matchAckIndexer.ty @!! go!"AckedIndex")) (Val #id))
  {{ RET (PairV #(matchOf pv id) #(decide (id ∈ pv))); progressMapOwn mp prs pv }}

end spec
end Tracker
end EtcdGrove
end Perennial
