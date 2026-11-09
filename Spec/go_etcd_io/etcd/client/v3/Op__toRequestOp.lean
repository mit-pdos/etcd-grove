/-
`(clientv3.Op).toRequestOp` (`client/v3/op.go`).

Users: `txn.Then`/`Else`, `Op.toTxnRequest`.

Proof sketch: by the type: `toRangeRequest.spec`, a fresh `PutRequest`/`DeleteRangeRequest`, `toTxnRequest.spec`; wrapped in a fresh `RequestOp` (`requestOpOwn_unfold`, `requestOneof`). Panics on a zero `Op` at any depth (premise `toReqOp`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Op__toRequestOp.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `op.toRequestOp()`: its `RequestOp`, owned (premise: no zero `Op` at any depth). -/
def Op.toRequestOp.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (dq : DFrac) (r : RequestOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦{dq} op ∗ opAt op o ∗ ⌜o.toReqOp = some r⌝ }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"toRequestOp")) (Val #()))
  {{ (p : Loc), RET #p; opp ↦{dq} op ∗ requestOpOwn p (DFrac.own 1) r }}

end spec

end ClientV3
end EtcdGrove
end Perennial
