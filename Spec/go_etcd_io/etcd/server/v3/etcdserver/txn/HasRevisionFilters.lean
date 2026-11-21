/-
`HasRevisionFilters` (`range.go`). Lean-first; see `InvRange.lean`, `RangeModel.lean`. The request at
any fraction of its rewritable fields, given back (`txn.rangeRequestAt`; auth-mediation M3, 2026-11-21:
the gRPC layer's `checkRangeStreamRequest` checks a streamed request it owns; was `rangeRequestIs`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RequestAt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `HasRevisionFilters(r)`: the request `r` (denoting `o`) has a revision filter. -/
abbrev txn.HasRevisionFilters.spec : Prop :=
  ∀ (r : Loc) (dq : DFrac) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.rangeRequestAt r dq o }}
    (App (Val (@! txn.HasRevisionFilters)) (Val #r))
  {{ RET #(txn.hasRevFilters o); txn.rangeRequestAt r dq o }}

end spec

end EtcdGrove
end Perennial
