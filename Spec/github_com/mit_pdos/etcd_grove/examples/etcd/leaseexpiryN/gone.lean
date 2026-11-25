/-
`gone(cli, id)` (`examples/etcd/leaseexpiryN/leaseexpiryN.go`; `notes/leaseN-plan.md`, 2026-11-16): the
listing of `cli`'s member polled (`leases`, `listed`, `time.Sleep` between polls) until it does not list
`id`. Lean-first (no Rocq counterpart).

**The triple:** for a client `cli` of the endpoint `addr` (`isNewClient`), with the listing registered
there at a lessor `γl`'s history (`etcdLeaseLeasesSpecLive`: a reply lists the lessor's leases at an
index at or after the caller's lower bound) and the lower bound `m` (`lessorLb γl m`): `gone` returns
`true` only if `id` is absent from the lessor at an index at or after `m` (`leaseAbsentFrom`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Defs
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiryN

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]

/-- See the file header. -/
abbrev gone.spec : Prop :=
  ∀
    (cl : Loc) (eps : List GoString) (V : client.WEnv GF) (γl : GName) (m : Nat) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN ∗
      isNewClient cl eps V ∗
      isGrpcRpcs eps go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpecLive γl) ∗
      lease.lessorLb γl m ∗
      ⌜errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.gone)) (Val #cl))
      (Val #id))
  {{ (b : Bool), RET #b; if b then lease.leaseAbsentFrom γl m id else True }}

end spec

end etcd_leaseexpiryN
end EtcdGrove
end Perennial
