/-
`(*clientv3.RangeStreamResponse).Err` (`client/v3/kv.go`).

Users: Kubernetes' store (`etcd3/store.go`: each chunk's `Err()`), `GetStreamToGetResponse`.

Proof sketch: returns the field.

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

/-- `r.Err()`: the chunk's terminal error (`nil` for a chunk of key-values). -/
def RangeStreamResponse.Err.spec : Prop :=
  ∀ (p : Loc) (v : go_etcd_io.etcd.client.v3.RangeStreamResponse) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ p ↦{dq} v }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.RangeStreamResponse.ty @!! go!"Err")) (Val #()))
  {{ RET #v.closeErr'; p ↦{dq} v }}

end spec

end ClientV3
end EtcdGrove
end Perennial
