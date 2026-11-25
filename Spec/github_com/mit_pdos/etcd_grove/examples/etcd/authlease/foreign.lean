/-
`foreign(cli, who, id)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9, checks 3–5): `who`
(`u` against root's lease, `v` against u's) is refused `Revoke(id)`, `TimeToLive(id)` with keys and
`Leases`, `id` holding a key `who` may not touch; each success panics. Lean-first (no Rocq counterpart).

**The triple:** with auth on (the revocation's result is the caller's only then), a client `cli` of
the member at `addr` whose attempts carry a token of `who`'s, the
member's Lease service with auth on, lower bounds `n` of its published auth index and `m` of its
lessor, the caller's resource `R` (kept), the caller's update of the revocation of `id` (at `who`'s
attempts) whose result `Qr` is impossible with `R`, and the caller's refutations, with `R`, of a
passed lease check at a token of `who`'s: over `id`'s keys from `m` on (`TimeToLive` with keys), and
over the keys of every lease of a listing at an index from `m` on (`Leases`). `foreign` returns `R`.
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
abbrev foreign.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (cli : Loc) (who addr : GoString) (id : w64) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γa : auth.AuthNames) (n m : Nat) (Qr : KVState → IProp GF) (R : IProp GF),
  who = go!"u" ∨ who = go!"v" → E.authOn = true →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease ∗ levelTok 0 ∗ (clientTokAt cli [addr] (akTokP γa who) ∗ etcdstart.etcdLeaseServedOn addr s E ρ ∗
      auth.authPubLbM E.authMode n ∗ lease.lessorLb (mvcc.api.mvccLeases E.γ) m ∗ R ∗
      □ (∀ (conn : Loc) (ctx : GrpcMd), attemptTokOk conn (akTokP γa who) -∗
          ⌜ctx = akOut who⌝ -∗ clientOpAuOn (srvTLSId s) E ρ conn ctx (.leaseRevoke id) Qr) ∗
      □ (∀ σ, Qr σ -∗ R ={⊤}=∗ False) ∗
      □ (∀ tok : Option GoString, akTokSeen γa who tok -∗
          leaseCheckFrom (srvTLSId s) E tok n (fun info =>
            leaseKeysVerdictFrom E.authMode n info (mvcc.api.mvccLeases E.γ) m id .read) -∗
          R ={⊤}=∗ False) ∗
      □ (∀ (tok : Option GoString) (i : Nat) (ids : List w64), ⌜m ≤ i⌝ -∗ akTokSeen γa who tok -∗
          lease.leaseIdsAt (mvcc.api.mvccLeases E.γ) i ids -∗
          leaseCheckFrom (srvTLSId s) E tok n (fun info => iprop([∗list] id' ∈ ids,
            leaseKeysVerdictFrom E.authMode n info (mvcc.api.mvccLeases E.γ) i id' .read)) -∗
          R ={⊤}=∗ False)) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.foreign)) (Val #cli))
      (Val #who)) (Val #id))
  {{ RET #(); levelTok 0 ∗ (R) }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
