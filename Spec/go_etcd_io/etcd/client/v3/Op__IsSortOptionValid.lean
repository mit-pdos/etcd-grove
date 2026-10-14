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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.IsSortOptionValid()` of an `Op` without a sort option: `true` (its other case reads
`etcdserverpb`'s enumeration maps, not specified here). -/
abbrev Op.IsSortOptionValid.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opFullAt opv o ∗
      ⌜o.base.sortSet = false⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"IsSortOptionValid")) (Val #()))
  {{ RET #true; True }}

end spec

end EtcdGrove
end Perennial
