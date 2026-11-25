/-
`grantPut(cli, k)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9): `cli.Lease.Grant` of
`grantTTL`, then `cli.Put(k, "v", WithLease(id))` of the granted id. Lean-first (no Rocq counterpart).

**The triple:** a client `cli` of the member at `addr` (`clientTokAt`, its attempts' tokens meeting
`P`) whose `LeaseGrant` and `Put` are etcd's with auth on, in the revocable lease mode; the caller's
grant update for every id (`Qg`), and a ghost step `Fix` that, once the grant returned the id `id`
(not `NoLease`) with `Qg id` of some state, turns the caller's `R` into `R' id` and the put's update
for that id (`Qp id`), every attempt's context without outgoing metadata. `true` returns the id, with
`R' id` and `Qp id` of some state; `false`, nothing.
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
abbrev grantPut.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (cli : Loc) (k addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (n : Nat) (F : mvcc.Log) (P : GoString → IProp GF) (Qg Qp : w64 → KVState → IProp GF)
    (R : IProp GF) (R' : w64 → IProp GF),
  E.authOn = true → ρ.kv.lm = .revocable → (∀ id : w64, opSizeOk (opPutModel k go!"v" [withLeaseM id])) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease ∗
      clientTokAt cli [addr] P ∗ auth.authPubLbM E.authMode n ∗
      isGrpcRpcMd addr go!"/etcdserverpb.Lease/LeaseGrant"
        (etcdLeaseGrantSpecOn (srvTLSId s) E ρ (mvcc.api.mvccLeases E.γ)) ∗
      isGrpcRpcMd addr go!"/etcdserverpb.KV/Put" (etcdPutSpecOn (srvTLSId s) E ρ cid mid) ∗
      srvApi.kvLogLb E.γs F ∗
      □ (∀ (conn : Loc) (ctx : GrpcMd) (id : w64),
          clientOpAuOn (srvTLSId s) E ρ conn ctx (.leaseGrant id grantTTLv) (Qg id)) ∗ R ∗
      (∀ id : w64, ⌜id ≠ W64 0⌝ -∗ (∃ σ, Qg id σ) -∗ R ={⊤}=∗ R' id ∗
        □ (∀ (conn : Loc) (ctx : GrpcMd), attemptTokOk conn P -∗ ⌜ctx = none⌝ -∗
          clientOpAuOn (srvTLSId s) E ρ conn ctx (.put (leasePutOp k id)) (Qp id))) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.grantPut)) (Val #cli))
      (Val #k))
  {{ (id : w64) (ok : Bool), RET (PairV #id #ok); ⌜ok = false⌝ ∨
      (⌜ok = true⌝ ∗ R' id ∗ ∃ σ, Qp id σ) }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
