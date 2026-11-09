/-
`clientv3.OpResponse.Txn` (`client/v3/kv.go`).

Users: leasing (`leasing/kv.go` `Do`'s result), the cache (`cache/cache.go`: `resp.Get()` of `Do`'s result).

Proof sketch: returns the field.

Changes: none (no old spec): added for the users named above.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `r.Txn()`: the `txn` field. -/
def OpResponse.Txn.spec : Prop :=
  ∀ (r : go_etcd_io.etcd.client.v3.OpResponse),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (r @!! go_etcd_io.etcd.client.v3.OpResponse.ty @!! go!"Txn")) (Val #()))
  {{ RET #r.txn'; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
