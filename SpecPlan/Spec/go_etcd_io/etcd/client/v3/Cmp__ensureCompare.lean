/-
`(*clientv3.Cmp).ensureCompare` (`client/v3/compare.go`).

Users: `Compare`, `Cmp.GetCompare`, `Cmp.WithRange`, `Cmp.WithPrefix`.

Proof sketch: a nil message replaced by a fresh zero one (persisted).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Cmp__ensureCompare.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `cmp.ensureCompare()`: the `Cmp` has a message (a zero `Compare` if it had none). -/
def Cmp.ensureCompare.spec : Prop :=
  ∀ (cp : Loc) (c : go_etcd_io.etcd.client.v3.Cmp) (m : Option EtcdModel.Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cp ↦ c ∗ cmpAt c m }}
    (App (Val (cp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Cmp.ty @!! go!"ensureCompare")) (Val #()))
  {{ RET #(); ∃ c' : go_etcd_io.etcd.client.v3.Cmp, cp ↦ c' ∗ cmpAt c' (some (m.getD Compare.zero)) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
