/-
`(*clientv3.Op).WithValueBytes` (`client/v3/op.go`).

Users: the `namespace` package (`client/v3/namespace`: prefixes the keys of the `Op`s it forwards); leasing reads, never writes.

Proof sketch: `opAt_unfold`; one store.

Changes: none (no old spec): added for the users named above.

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

/-- `op.WithValueBytes(b)`: the value set to the caller's bytes (read-only from now on). -/
def Op.WithValueBytes.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (b : GoSlice) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦ op ∗ opAt op o ∗ b ↦*□ k }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"WithValueBytes")) (Val #b))
  {{ RET #(); ∃ op' : go_etcd_io.etcd.client.v3.Op, opp ↦ op' ∗ opAt op' { o with val := k } }}

end spec

end ClientV3
end EtcdGrove
end Perennial
