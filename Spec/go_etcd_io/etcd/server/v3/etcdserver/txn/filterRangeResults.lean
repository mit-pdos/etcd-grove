/-
`filterRangeResults` (`range.go`): the revision filters.
Lean-first; see `InvRange.lean`, `RangeModel.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `filterRangeResults(rr, r)`: the key-values passing the request's revision filters
(`kvFilterOk`), in order. -/
abbrev txn.filterRangeResults.spec : Prop :=
  ∀ (rr r : Loc) (o : OpFull) (rev count : w64) (vs : List EtcdKv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.rangeResultIs rr rev count vs ∗ txn.rangeRequestIs r o }}
    (App (App (Val (@! txn.filterRangeResults)) (Val #rr)) (Val #r))
  {{ RET #(); txn.rangeResultIs rr rev count (vs.filter (kvFilterOk o)) }}

end spec

end EtcdGrove
end Perennial
