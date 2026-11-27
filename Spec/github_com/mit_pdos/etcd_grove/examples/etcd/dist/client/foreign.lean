/-
`foreign(cli, who, id, forbidden)` (`examples/etcd/dist/client/authlease.go`; authlease's checks 3-5, adapted):
three lease calls by a user (`u` or `v`) about a lease `id` of another principal holding the key `forbidden`, which
the user may not write or read: `Revoke(id)`, which must be refused (`refused` panics on success);
`TimeToLive(id, WithAttachedKeys())`, which panics only if it succeeds and returns the key `forbidden`; and
`Leases()`, its result ignored (its replies carry lease IDs only). Auth on, revocable mode, at the cluster view,
`cli` a user client (`userCli`) of the endpoint `addr` serving member `mid`: each call over its `Lease_*On_dist`
contract at `mid`, which takes a published auth index `n₀` and a lower bound `m₀` of `mid`'s lessor. As the
single-process `etcd_authlease.foreign.spec`, the caller refutes what would panic, with its resource `R`
(returned): `Revoke`'s success (its result `Qr σ` and its check `writeCheckedD`), and member `mid`'s read verdict
granting the principal the key `forbidden` at a published index `n ≥ n₀` (what `TimeToLive`'s post says of each
returned key). Lean-first (no Rocq counterpart); F7 stage S5, the TimeToLive check F7 (fork).
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
    (cl : Loc) (who addr : GoString) (id : w64) (forbidden : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
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
      □ (∀ n : Nat, ⌜n₀ ≤ n⌝ -∗
          leaseCheckD (Γ.au mid) (principalOf cfg) n
            (fun info => auth.permVerdictFrom (.on (Γ.au mid)) n info forbidden [] .read GoInterface.nil) -∗
          R ={⊤}=∗ False) }}
    (App (App (App (App (Val (@! client.foreign)) (Val #cl)) (Val #who)) (Val #id)) (Val #forbidden))
  {{ RET #(); levelTok 0 ∗ R }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
