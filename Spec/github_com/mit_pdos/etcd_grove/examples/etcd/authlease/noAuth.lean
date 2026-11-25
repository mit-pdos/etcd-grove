/-
`noAuth(cli, who, id)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9, check 1): `who`
(`anon`, the client with no token, or `bad`, the one with the invalid token) is refused `Grant`,
`Revoke(id)`, `TimeToLive(id)` without and with keys, and `Leases`; each success panics. Lean-first (no
Rocq counterpart).

**The triple:** a client `cli` of the member at `addr` whose attempts carry a token of `who`'s
(`clientTokAt` at `akTokP γa who`), the member's Lease service with auth on (`etcdLeaseServedOn`), lower
bounds `n` of its published auth index and `ml` of its lessor; no lease check passes for a token of
`who`'s relative to `n` (the caller's refutation, from the auth state fixed after the set-up); the
caller's updates of the grant (any id) and of the revocation of `id` (at `who`'s attempts): `noAuth`
returns.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Env

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]
/-- See the file header. -/
abbrev noAuth.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (cli : Loc) (who addr : GoString) (id : w64) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γa : auth.AuthNames) (n ml : Nat) (Qg : w64 → KVState → IProp GF) (Qr : KVState → IProp GF),
  who = go!"anon" ∨ who = go!"bad" →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease ∗ levelTok 0 ∗ (clientTokAt cli [addr] (akTokP γa who) ∗ etcdstart.etcdLeaseServedOn addr s E ρ ∗
      auth.authPubLbM E.authMode n ∗ lease.lessorLb (mvcc.api.mvccLeases E.γ) ml ∗
      □ (∀ (tok : Option GoString) (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF),
          akTokSeen γa who tok -∗ leaseCheckFrom (srvTLSId s) E tok n K ={⊤}=∗ False) ∗
      □ (∀ (conn : Loc) (ctx : GrpcMd) (id' : w64),
          clientOpAuOn (srvTLSId s) E ρ conn ctx (.leaseGrant id' grantTTLv) (Qg id')) ∗
      □ (∀ (conn : Loc) (ctx : GrpcMd), attemptTokOk conn (akTokP γa who) -∗
          ⌜ctx = akOut who⌝ -∗ clientOpAuOn (srvTLSId s) E ρ conn ctx (.leaseRevoke id) Qr)) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.noAuth)) (Val #cli))
      (Val #who)) (Val #id))
  {{ RET #(); levelTok 0 ∗ (True) }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
