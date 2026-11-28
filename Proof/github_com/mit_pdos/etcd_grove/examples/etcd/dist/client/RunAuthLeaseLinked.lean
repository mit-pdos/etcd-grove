/- Lean-first (no Rocq counterpart).

# The authLease workload's orchestrator, linked (#50 F7, option "(fork)", `notes/etcd-dist-f7-fork.md`, "Handoff K-5")

`RunAuthLease.spec` from `RunAuthLease.wp_proof`, over `RunAuthLinked`'s `wp_newClientA`, `wp_SetUpDist`,
`wp_barriersA` and `wp_newUserClient`, the leaf proofs (`grantPut`, `noAuth`, `foreign`, `ownLease`, `absent`,
`refused`, `reqCtx`, `ended`, `checked`), the client library's (`WithLease`, `WithAttachedKeys`, `OpPut`, `Then` at
plain operations, `client_Txn_dist.law` from its `_holds`) and the auth-on interim contracts (`Txn_CommitOn_dist`,
`KV_PutOn_dist`, `KV_GetOn_dist`, `Lease_{Grant,Revoke,TimeToLive,Leases}On_dist`). `MainReady`'s kind-6 arm takes
it (`DispatchLinked`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunAuthLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunAuthLease
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.grantPut
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.noAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.foreign
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ownLease
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.absent
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.refused
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reqCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseRevokeOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseTimeToLiveOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TxnCommitOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.CallDistLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Link
public import Proof.go_etcd_io.etcd.client.v3.WithLease
public import Proof.go_etcd_io.etcd.client.v3.WithAttachedKeys
public import Proof.go_etcd_io.etcd.client.v3.TxnPlainSpec
public import Proof.go_etcd_io.etcd.client.v3.Link
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
variable [auth_sem : github_com.mit_pdos.etcd_grove.examples.lib.authwork.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [rem_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [NaInvG GF]

/-- The per-request context of the lease checks, linked. -/
theorem wp_reqCtxD : reqCtx.spec (GF := GF) (hG := hG) :=
  reqCtx.wp_proof context.WithTimeoutBackgroundMd.wp_proof context.wp_ErrAny
    etcd_auth.metadata.wp_AppendToOutgoingContext

/-- **The authLease workload's orchestrator, linked** (see the file header). -/
theorem wp_RunAuthLease : RunAuthLease.spec (GF := GF) (hG := hG) :=
  RunAuthLease.wp_proof wp_newClientA wp_SetUpDist wp_barriersA wp_newUserClient
    (grantPut.wp_proof context.WithTimeoutBackgroundMd.wp_proof context.wp_ErrAny WithLease.wp_proof
      etcd_dist.authd.Lease_GrantOn_dist.wp_proof etcd_dist.authd.KV_PutOn_dist.wp_proof)
    (noAuth.wp_proof wp_reqCtxD refused.wp_proof WithAttachedKeys.wp_proof
      etcd_dist.authd.Lease_GrantOn_dist.wp_proof etcd_dist.authd.Lease_RevokeOn_dist.wp_proof
      etcd_dist.authd.Lease_TimeToLiveOn_dist.wp_proof etcd_dist.authd.Lease_LeasesOn_dist.wp_proof)
    (foreign.wp_proof wp_reqCtxD refused.wp_proof WithAttachedKeys.wp_proof
      etcd_dist.authd.Lease_RevokeOn_dist.wp_proof etcd_dist.authd.Lease_TimeToLiveOn_dist.wp_proof
      etcd_dist.authd.Lease_LeasesOn_dist.wp_proof)
    (ownLease.wp_proof context.WithTimeoutBackgroundMd.wp_proof context.wp_ErrAny
      etcd_dist.authd.Lease_GrantOn_dist.wp_proof)
    (absent.wp_proof context.WithTimeoutBackgroundMd.wp_proof context.wp_ErrAny
      etcd_dist.authd.KV_GetOn_dist.wp_proof)
    refused.wp_proof ended.wp_proof checked.wp_proof context.WithTimeoutBackgroundMd.wp_proof context.wp_ErrAny
    WithLease.wp_proof client.v3.wp_OpPut (etcd_txnlin.client_Txn_dist_law_holds client.v3.kv.wp_Txn)
    (txn.Then.spec_plain client.v3.txn.wp_Then) etcd_dist.authd.Txn_CommitOn_dist.wp_proof
    etcd_dist.authd.KV_PutOn_dist.wp_proof etcd_dist.authd.KV_GetOn_dist.wp_proof
    etcd_dist.authd.Lease_RevokeOn_dist.wp_proof

end links

end etcd_dist_client
end EtcdGrove
end Perennial
