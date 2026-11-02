/-
`(*clientv3.LeaseOp).applyOpts(opts)` (`client/v3/op.go`; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.applyOpts(opts)`: the options applied in order (`leaseKeysFold`); the lease ID unchanged. -/
abbrev LeaseOp.applyOpts.spec : Prop :=
  ∀ (p : Loc) (op : go_etcd_io.etcd.client.v3.LeaseOp) (sl : GoSlice) (gs : List (Bool → Bool)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ p ↦ op ∗ leaseOptsAt sl gs }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.LeaseOp.ty @!! go!"applyOpts"))
      (Val #sl))
  {{ RET #(); p ↦ { op with attachedKeys' := leaseKeysFold gs op.attachedKeys' } }}

end spec

end EtcdGrove
end Perennial
