/-
`rangeSortOrder` (`range.go`). Lean-first; see `InvRange.lean`, `RangeModel.lean`.
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

/-- `rangeSortOrder(r)`: the order the results are sorted in (`r.SortOrder`, with `NONE` read as
`ASCEND` for a non-key target: `rangeSortOrderOf`). -/
abbrev txn.rangeSortOrder.spec : Prop :=
  ∀ (r : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗
      txn.rangeRequestIs r o }}
    (App (Val (@! txn.rangeSortOrder)) (Val #r))
  {{ (so : w32), RET #so; ⌜W64 (sint.Z so) = txn.rangeSortOrderOf o⌝ }}

end spec

end EtcdGrove
end Perennial
