/-
`(*clientv3.Cmp).GetCompare` (`client/v3/compare.go`).

Users: `txn.If`, `Op.toTxnRequest`, leasing (`leasing/txn.go`: the messages of its comparisons).

Proof sketch: `Cmp.ensureCompare.spec`, the field.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Cmp__GetCompare.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

verify-round: the fresh `*pb.Compare` (its `protoRest` from `protoRest_zero` at `own 1`) is made read-only for `cmpAt` by `protoRest_persist` (A1-provability F6: the sketch had no law for it).

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

/-- `cmp.GetCompare()`: its message, read-only (a zero one made if it had none). -/
def Cmp.GetCompare.spec : Prop :=
  ∀ (cp : Loc) (c : go_etcd_io.etcd.client.v3.Cmp) (m : Option EtcdModel.Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cp ↦ c ∗ cmpAt c m }}
    (App (Val (cp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"GetCompare")) (Val #()))
  {{ (p : Loc), RET #p; ∃ c' : go_etcd_io.etcd.client.v3.Cmp, cp ↦ c' ∗ cmpAt c' (some (m.getD Compare.zero)) ∗
      compareOwn p DFrac.discard (m.getD Compare.zero) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
