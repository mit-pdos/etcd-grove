/-
`clientv3.Op.isWrite()` (`client/v3/op.go`, translated for the vertical slice's unit V2). Lean-first (no Rocq counterpart).
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

/-- `op.isWrite()` of an operation tree: whether it is not a range, for a nested transaction
whether some operation of either branch writes (`OpT.isWrite`). -/
abbrev Op.isWrite.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (t : OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opTAtC false opv t }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"isWrite")) (Val #()))
  {{ RET #(OpT.isWrite t); True }}

end spec

end EtcdGrove
end Perennial
