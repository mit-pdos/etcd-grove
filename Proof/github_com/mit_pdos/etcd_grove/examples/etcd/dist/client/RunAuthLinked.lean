/- Lean-first (no Rocq counterpart).

# The auth workload's orchestrator, linked (#50 F7 S12, `notes/etcd-dist-f7.md`, "Handoff W-6")

`RunAuth.spec` (`RunAuth.specWith` at `principalsShare`) from `RunAuth.wp_proof`, over `PrincipalsLinked`'s
`wp_remotePrincipals` and `wp_newClientA`/`wp_newUserClient`, the dist set-up (`SetUp.wp_proof_dist` over the
auth-on interim contracts), the barriers and the history checks. `WatchOn_dist` stays the lead's interim axiom.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.PrincipalsLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.barrier
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.barriers
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.collectFor
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.SetUpDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthUserAddDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthUserGrantRoleDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthRoleAddDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthRoleGrantPermissionDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthAuthEnableDist
public import Proof.context.WithTimeoutBackgroundMd
public import Proof.go_etcd_io.etcd.client.v3.WithPrefix
public import Proof.go_etcd_io.etcd.client.v3.getPrefix
public import Proof.go_etcd_io.etcd.client.v3.WithRev
public import Proof.go_etcd_io.etcd.client.v3.WithRange
public import Perennial.Proof.context.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open etcd_dist
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section links
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [auth_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [rem_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [NaInvG GF]

/-- authkv's set-up at the cluster view, linked over the auth-on interim contracts. -/
theorem wp_SetUpDist : etcd_auth.SetUp.spec_dist (GF := GF) (hG := hG) :=
  etcd_auth.SetUp.wp_proof_dist context.WithTimeoutBackgroundMd.wp_proof context.wp_ErrAny etcd_auth.wp_Principals
    etcd_auth.wp_keyOf etcd_dist.authd.KV_PutOn_dist.wp_proof etcd_dist.authd.Auth_UserAdd_dist.wp_proof
    etcd_dist.authd.Auth_UserGrantRole_dist.wp_proof etcd_dist.authd.Auth_RoleAdd_dist.wp_proof
    etcd_dist.authd.Auth_RoleGrantPermission_dist.wp_proof etcd_dist.authd.Auth_AuthEnable_dist.wp_proof

/-- Root's barrier at every member, linked. -/
theorem wp_barriersA : barriers.spec (GF := GF) (hG := hG) :=
  barriers.wp_proof (barrier.wp_proof wp_newUserClient context.WithTimeoutBackgroundMd.wp_proof context.wp_ErrAny
    etcd_dist.authd.KV_GetOn_dist.wp_proof client.v3.Client.wp_Close)

/-- **The auth workload's orchestrator, linked** at `principalsShare` (`WatchOn_dist` the interim axiom). -/
theorem wp_RunAuth : RunAuth.spec (GF := GF) (hG := hG) :=
  RunAuth.wp_proof _ wp_newClientA wp_SetUpDist wp_barriersA wp_newUserClient wp_remotePrincipals
    ended.wp_proof checked.wp_proof context.WithTimeoutBackgroundMd.wp_proof context.wp_ErrAny
    etcd_dist.authd.KV_PutOn_dist.wp_proof etcd_dist.authd.WatchOn_dist.wp_proof
    (WithPrefix.wp_proof getPrefix.wp_proof) WithRev.wp_proof WithRange.wp_proof
    (collectFor.wp_proof _root_.Perennial.time.wp_AfterFunc _root_.Perennial.time.Timer.wp_Stop etcdstart.wp_Collect)
    etcd_auth.wp_CheckHistory etcd_auth.wp_LastIn etcd_auth.wp_Permitted

end links

end etcd_dist_client
end EtcdGrove
end Perennial
