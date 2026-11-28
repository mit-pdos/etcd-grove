/-
`ownLease(cli)` (`examples/etcd/dist/client/authlease.go`): a lease of TTL `maxLeaseTTL` granted through `cli`, in
a context with the request timeout; whether the grant returned. Auth on, revocable mode, at the cluster view, `cli`
a user client (`userCli`) of the endpoint `addr` serving member `mid`: the grant over
`etcd_dist.authd.Lease_GrantOn_dist` at `mid`, its update a persistent offer (`writeAuD`) at every id. On success,
a lower bound of member `mid`'s lessor (what `foreign`'s lessor reads there take). The lease is the principal's
own and holds no key: nothing else of it is claimed. Lean-first (no Rocq counterpart); F7 (fork), option (3).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.authd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev ownLease.spec : Prop :=
  ∀ [π : NetProtoGS] (cl : Loc) (addr : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel) (n₀ : Nat)
    (Qg : w64 → KVState → IProp GF),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  Γ.auth = true → Γ.kv.lm = .revocable → γR.raft.log = Γ.kv.rlog →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ userCli cl addr V cfg ∗ etcdAddrAt (Gg := hG.goose_globalGS) addr Γ mid ∗
      srvReqLogLb γR L₀ ∗ auth.authPubLbM (.on (Γ.au mid)) n₀ ∗
      □ (∀ id : w64, writeAuD Γ.kv (principalOf cfg) (.leaseGrant id (W64 9000000000)) L₀ (Qg id)) }}
    (App (Val (@! client.ownLease)) (Val #cl))
  {{ (ok : Bool), RET #ok; levelTok 0 ∗ (⌜ok = false⌝ ∨
      (⌜ok = true⌝ ∗ ∃ m : Nat, lease.lessorLb (Γ.ls mid) m)) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
