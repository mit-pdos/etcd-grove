/-
`(*clientv3.LeaseOp).applyOpts` (`client/v3/op.go`).

Users: `toLeaseTimeToLiveRequest`.

Proof sketch: a loop: `leaseOptAt_call` per closure.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/LeaseOp__applyOpts.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `op.applyOpts(opts)`: the lease options applied, in order. -/
def LeaseOp.applyOpts.spec : Prop :=
  ∀ (p : Loc) (op : go_etcd_io.etcd.client.v3.LeaseOp) (sl : GoSlice) (gs : List (Bool → Bool)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ p ↦ op ∗ leaseOptsAt sl gs }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.LeaseOp.ty @!! go!"applyOpts")) (Val #sl))
  {{ RET #(); leaseOptsAt sl gs ∗ ∃ op' : go_etcd_io.etcd.client.v3.LeaseOp, p ↦ op' ∗
      ⌜op'.id' = op.id' ∧ op'.attachedKeys' = gs.foldl (fun b g => g b) op.attachedKeys'⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
