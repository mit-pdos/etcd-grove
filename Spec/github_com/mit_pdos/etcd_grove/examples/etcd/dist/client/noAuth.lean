/-
`noAuth(cli, who, id)` (`examples/etcd/dist/client/authlease.go`; authlease's, copied): five lease calls by a
principal with no user (anonymous, or a bad token): `Grant`, `Revoke(id)`, `TimeToLive(id)` with and without
attached keys, `Leases`; each must be refused (`refused` panics on success). Auth on, revocable mode, at the
cluster view, `cli` a user client (`userCli`) of the endpoint `addr` serving member `mid`, with no user in its
configuration (`principalOf cfg = none`): each call over its `Lease_*On_dist` contract at `mid`, whose success
carries member `mid`'s `leaseCheckD … n` at a published index `n ≥ n₀`; the caller refutes every such check (as
the single-process `etcd_authlease.noAuth.spec`; its caller does so from the frozen floor,
`authFloorD_frozen`/`leaseCheckD_none_frozen`). The two writes' updates are the caller's persistent offers
(`writeAuD`). Lean-first (no Rocq counterpart); F7 stage S5.
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
abbrev noAuth.spec : Prop :=
  ∀ [π : NetProtoGS] [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (cl : Loc) (who addr : GoString) (id : w64) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel) (n₀ m₀ : Nat)
    (Qg : w64 → KVState → IProp GF) (Qr : KVState → IProp GF),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  Γ.auth = true → Γ.kv.lm = .revocable → γR.raft.log = Γ.kv.rlog → principalOf cfg = none →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ userCli cl addr V cfg ∗ etcdAddrAt (Gg := hG.goose_globalGS) addr Γ mid ∗
      srvReqLogLb γR L₀ ∗ auth.authPubLbM (.on (Γ.au mid)) n₀ ∗ lease.lessorLb (Γ.ls mid) m₀ ∗
      □ (∀ id' : w64, writeAuD Γ.kv (principalOf cfg) (.leaseGrant id' (W64 9000000000)) L₀ (Qg id')) ∗
      writeAuD Γ.kv (principalOf cfg) (.leaseRevoke id) L₀ Qr ∗
      □ (∀ (n : Nat) (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF), ⌜n₀ ≤ n⌝ -∗
          leaseCheckD (Γ.au mid) (principalOf cfg) n K ={⊤}=∗ False) }}
    (App (App (App (Val (@! client.noAuth)) (Val #cl)) (Val #who)) (Val #id))
  {{ RET #(); levelTok 0 }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
