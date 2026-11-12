/-
`(*clientv3.Op).applyOpts` (`client/v3/op.go`).

Users: the `Op` constructors.

Proof sketch: a loop over the slice: `optAt_call` per closure, in order.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Op__applyOpts.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `op.applyOpts(opts)`: every option applied, in order; the options given back. -/
def Op.applyOpts.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (sl : GoSlice) (gs : List (OpM → OpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦ op ∗ opAt op o ∗ optsAt sl gs }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"applyOpts")) (Val #sl))
  {{ RET #(); optsAt sl gs ∗ ∃ op' : go_etcd_io.etcd.client.v3.Op, opp ↦ op' ∗ opAt op' (applyOptsM gs o) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
