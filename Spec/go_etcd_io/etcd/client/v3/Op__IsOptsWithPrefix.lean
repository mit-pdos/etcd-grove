/-
`(clientv3.Op).IsOptsWithPrefix` (`client/v3/op.go`).

Users: leasing (`leasing/kv.go`, `leasing/txn.go`, `leasing/cache.go`, `leasing/util.go`: it
inspects every `Op` it forwards: `IsGet`, `IsPut`, `IsDelete`, `IsTxn`, `KeyBytes`, `RangeBytes`,
`IsSerializable`, `IsKeysOnly`, `IsCountOnly`, `Txn()`), the cache (`cache/cache.go`
`validateGet`/`validateWatch`: `Rev`, `IsSerializable`, `IsProgressNotify`, `Limit`, `IsCountOnly`,
`IsSortSet`, the revision filters, `IsPrevKV`, `IsFragment`, `IsCreatedNotify`, `IsFilterPut`,
`IsFilterDelete`, `RangeBytes`). Snippet: `clientv3kv/ops.go` (`ReqOpGetters`).

Proof sketch: `opAt_unfold`; loads the field.

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

/-- `op.IsOptsWithPrefix()`: the field. -/
def Op.IsOptsWithPrefix.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦{dq} op ∗ opAt op o }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"IsOptsWithPrefix")) (Val #()))
  {{ RET #(o.isOptsWithPrefix); opp ↦{dq} op }}

end spec

end ClientV3
end EtcdGrove
end Perennial
