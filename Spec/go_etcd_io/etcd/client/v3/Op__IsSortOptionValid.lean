/-
`clientv3.Op.IsSortOptionValid()` (`client/v3/op.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.IsSortOptionValid()`: `sortValid o` (no sort option, or its order's and target's `int32`
values are keys of `etcdserverpb`'s enumeration maps, `sortNamesOk`; the vertical slice's unit V2:
C1 specified the case without a sort option only). -/
abbrev Op.IsSortOptionValid.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opFullAt opv o ∗
      sortNamesIf o.base.sortSet }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"IsSortOptionValid")) (Val #()))
  {{ RET #(sortValid o); True }}

end spec

end EtcdGrove
end Perennial
