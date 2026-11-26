/-
`foreign(cli, who, id)` (`examples/etcd/dist/client/authlease.go`; authlease's, copied): three lease calls by a
user (`u` or `v`) about a lease `id` holding a key the user may not write or read: `Revoke(id)`,
`TimeToLive(id, WithAttachedKeys())` and `Leases()`; each must be refused (`refused` panics on success). Auth on,
revocable mode, at the cluster view, `cli` a user client (`userCli`) of the endpoint `addr` serving member `mid`:
each call over its `Lease_*On_dist` contract at `mid`. As the single-process `etcd_authlease.foreign.spec`, the
caller refutes each success, with its resource `R` (returned): `Revoke`'s (its result `Qr σ` and its check
`writeCheckedD`), `TimeToLive`'s (member `mid`'s check over `id`'s attached keys at a published index `n ≥ n₀`
and its lessor's index `j ≥ m₀`) and `Leases`' (the check over every listed lease's keys, the listing at `j`).
Lean-first (no Rocq counterpart); F7 stage S5.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
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
abbrev foreign.spec : Prop :=
  ∀ [π : NetProtoGS] [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (cl : Loc) (who addr : GoString) (id : w64) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (cfg : go_etcd_io.etcd.client.v3.Config) (γR : ServerRaftNames) (L₀ : List EntryModel) (n₀ m₀ : Nat)
    (Qr : KVState → IProp GF) (R : IProp GF),
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → (∀ a b : w64, Γ.ls a = Γ.ls b → a = b) →
  Γ.auth = true → Γ.kv.lm = .revocable → γR.raft.log = Γ.kv.rlog →
  (who = go!"bad" → principalOf cfg = none) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ userCli cl addr V cfg ∗ etcdAddrAt (Gg := hG.goose_globalGS) addr Γ mid ∗
      srvReqLogLb γR L₀ ∗ auth.authPubLbM (.on (Γ.au mid)) n₀ ∗ lease.lessorLb (Γ.ls mid) m₀ ∗ R ∗
      writeAuD Γ.kv (principalOf cfg) (.leaseRevoke id) L₀ Qr ∗
      □ (∀ σ : KVState, Qr σ -∗ writeCheckedD [addr] Γ γR (principalOf cfg) (irrLeaseRevoke id) L₀ -∗
          R ={⊤}=∗ False) ∗
      □ (∀ (n j : Nat), ⌜n₀ ≤ n ∧ m₀ ≤ j⌝ -∗
          leaseCheckD (Γ.au mid) (principalOf cfg) n
            (fun info => leaseKeysVerdictFrom (.on (Γ.au mid)) n info (Γ.ls mid) j id .read) -∗
          R ={⊤}=∗ False) ∗
      □ (∀ (n j : Nat) (ids : List w64), ⌜n₀ ≤ n ∧ m₀ ≤ j⌝ -∗ lease.leaseIdsAt (Γ.ls mid) j ids -∗
          leaseCheckD (Γ.au mid) (principalOf cfg) n
            (fun info => iprop([∗list] id' ∈ ids,
              leaseKeysVerdictFrom (.on (Γ.au mid)) n info (Γ.ls mid) j id' .read)) -∗
          R ={⊤}=∗ False) }}
    (App (App (App (Val (@! client.foreign)) (Val #cl)) (Val #who)) (Val #id))
  {{ RET #(); levelTok 0 ∗ R }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
