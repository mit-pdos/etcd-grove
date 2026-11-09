/-
`(*leaseKey).get` (`cache.go`): a fresh copy of the cached response for the get `op` (the header,
`More`, `Count`; the key-value unless the get's filters exclude it, its value dropped if keys-only).
Proof sketch: `copyGetResponseMetadataOnly`, the getters, `copyKeyValue`. Changes: from `specs-ref`'s
`leaseKey__get.lean`: over `cachedRespAt` and `leaseGetM` (was the cache's entry record).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `lk.get(op)`: `leaseGetM o m`, fresh; the cached response read only. -/
def leaseKey.get.spec : Prop :=
  ∀ (lkp : Loc) (dq : DFrac) (lk : go_etcd_io.etcd.client.v3.leasing.leaseKey) (q : Qp)
    (m : RangeRespM) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lkp ↦{dq} lk ∗ cachedRespAt lk.response' q m ∗ opAt op o }}
    (App (Val (lkp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseKey.ty @!! go!"get")) (Val #op))
  {{ (ret : Loc), RET #ret; lkp ↦{dq} lk ∗ cachedRespAt lk.response' q m ∗
      ∃ m' : RangeRespM, rangeRespOwn ret (DFrac.own 1) m' ∗ ⌜m' = leaseGetM o m⌝ }}

end spec

end Leasing
end EtcdGrove
end Perennial
