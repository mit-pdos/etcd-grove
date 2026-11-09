/-
`(*clientv3.Cmp).Clone` (`client/v3/compare.go`).

Users: `Compare`, `Cmp.WithRange`, `Cmp.WithPrefix`, `txn.If`, `OpTxn`, `Op.toTxnRequest`.

Proof sketch: `cmpAt_unfold`; a zero `Cmp` for a nil message, else `cloneCompare.spec` (persisted).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Cmp__Clone.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

verify-round: the fresh `*pb.Compare` (its `protoRest` from `protoRest_zero` at `own 1`) is made read-only for `cmpAt` by `protoRest_persist` (A1-provability F6: the sketch had no law for it).

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

/-- `cmp.Clone()`: a `Cmp` of the same comparison, of its own message. -/
def Cmp.Clone.spec : Prop :=
  ∀ (cp : Loc) (c : go_etcd_io.etcd.client.v3.Cmp) (m : Option EtcdModel.Compare) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cp ↦{dq} c ∗ cmpAt c m }}
    (App (Val (cp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"Clone")) (Val #()))
  {{ (c' : go_etcd_io.etcd.client.v3.Cmp), RET #c'; cp ↦{dq} c ∗ cmpAt c' m }}

end spec

end ClientV3
end EtcdGrove
end Perennial
