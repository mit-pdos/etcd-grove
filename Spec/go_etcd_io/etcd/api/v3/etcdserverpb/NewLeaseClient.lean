/-
`etcdserverpb.NewLeaseClient(cc)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated Lease stub;
item 1, the client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease

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

/-- `NewLeaseClient(cc)`: a new `*leaseClient` whose `cc` is `cc` (read-only), as a `LeaseClient`. -/
abbrev NewLeaseClient.spec : Prop :=
  ∀ (cc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb }}
    (App (Val (@! etcdserverpb.NewLeaseClient)) (Val #cc))
  {{ (v : GoInterface), RET #v; ∃ lc : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType etcdserverpb.leaseClient.ty) #lc⌝ ∗
      structFieldRef etcdserverpb.leaseClient go!"cc" lc ↦□ cc }}

end spec

end EtcdGrove
end Perennial
