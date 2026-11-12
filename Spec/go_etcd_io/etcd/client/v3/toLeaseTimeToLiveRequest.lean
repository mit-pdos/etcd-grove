/-
`clientv3.toLeaseTimeToLiveRequest(id, opts...)` (`client/v3/op.go`; the closed lease example, `notes/lease-ex-plan.md`). Lean-first (no
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

/-- `toLeaseTimeToLiveRequest(id, opts...)`: a new request (owned) for the lease `id`, its `Keys` what
the options leave of `false` (`WithAttachedKeys` sets it), the rest zero. -/
abbrev toLeaseTimeToLiveRequest.spec : Prop :=
  ∀ (id : w64) (sl : GoSlice) (gs : List (Bool → Bool)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ leaseOptsAt sl gs }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.toLeaseTimeToLiveRequest)) (Val #id)) (Val #sl))
  {{ (l : Loc), RET #l; l ↦ { (zeroValDef : etcdserverpb.LeaseTimeToLiveRequest) with
      ID' := id, Keys' := leaseKeysFold gs false } }}

end spec

end EtcdGrove
end Perennial
