/-
`clientv3.NewOp` (`client/v3/op.go`).

Users: `IsOptsWithPrefix`, `IsOptsWithFromKey`.

Proof sketch: a fresh `Op{key: []byte("")}`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/NewOp.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `NewOp()`: a fresh pointer to an `Op` of no type and empty key. -/
def NewOp.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewOp)) (Val #()))
  {{ (p : Loc), RET #p; ∃ op : go_etcd_io.etcd.client.v3.Op, p ↦ op ∗ opAt op OpM.newOp }}

end spec

end ClientV3
end EtcdGrove
end Perennial
