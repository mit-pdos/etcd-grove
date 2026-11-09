/-
`sortRangeResults(rr, r, lg)` (`range.go`), internal. **Proof sketch.** The sorter by target (the
`kvSortBy*` specs; a `Less` of numbers is the signed order for values in `[0, 2 ^ 63)`: `kvFits`),
`sort.Sort` (Perennial's `sort.Sort.spec`, at most `2 ^ 62` elements: kept here, local, the size
fact mvcc's `Range` gives), made a function by `goSort` (its functional spec: a Perennial change,
`batch-3b.md`). An unknown target is `lg.Panic`: excluded by `targetOk`. Old spec: `sortSmall`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `sortRangeResults(rr, r, lg)`: the key-values `sortOut`. -/
def sortRangeResults.spec : Prop :=
  ∀ (rr r : Loc) (dq : DFrac) (rm : RangeReq) (lg : Loc) (kvs : List KV) (rev c : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Zap.isLogger lg ∗ rrOwn rr kvs rev c ∗ rangeReqOwn r dq rm ∗
      ⌜targetOk rm ∧ kvs.length ≤ 2 ^ 62⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.sortRangeResults)) (Val #rr)) (Val #r)) (Val #lg))
  {{ RET #(); rrOwn rr (sortOut rm kvs) rev c ∗ rangeReqOwn r dq rm }}

end spec
end Txn
end EtcdGrove
end Perennial
