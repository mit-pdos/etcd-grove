/-
`(clientv3.Op).isWrite` (`client/v3/op.go`).

Users: `txn.Then`/`Else` (`isWrite`)

Proof sketch: `opAt_unfold`; recursion over the branches' `opsAt`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Op__isWrite.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `op.isWrite()`: not a range; a transaction with a write in a branch. -/
def Op.isWrite.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦{dq} op ∗ opAt op o }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"isWrite")) (Val #()))
  {{ RET #(o.isWrite); opp ↦{dq} op }}

end spec

end ClientV3
end EtcdGrove
end Perennial
