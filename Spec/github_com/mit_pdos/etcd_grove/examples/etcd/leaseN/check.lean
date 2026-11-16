/-
`check(addr, lg)` (`examples/etcd/leaseN/leaseN.go`; `notes/leaseN-plan.md`, 2026-11-16): the lease
example's two reads through a new client of the member at `addr`. Lean-first (no Rocq counterpart).

**The triple:** with etcd's lease reads registered at `addr` (`client.etcdLeaseReadAt`: `TimeToLive` and
`Leases` at etcd's specs, which every served member registers, `etcdstart.kv_lease_served`), a plain
endpoint, `check` returns (`V`: the client's watch environment `NewClient`'s spec takes, which `check`
does not use): it does not panic, so a listing that answered listed no lease twice and a
`TimeToLive(7)` that answered was about lease `7`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Base
public import Proof.go_etcd_io.etcd.client.v3.LeaseReadServed
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseN

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]

/-- See the file header. -/
abbrev check.spec : Prop :=
  ∀ [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (addr : GoString) (lg : Loc) (V : client.WEnv GF),
  plainEndpoint addr → threadBound GF ≤ 2 ^ 31 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN ∗
      zapLoggerOk lg ∗ client.etcdLeaseReadAt addr }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.check)) (Val #addr))
      (Val #lg))
  {{ (b : Bool), RET #b; True }}

end spec

end etcd_leaseN
end EtcdGrove
end Perennial
