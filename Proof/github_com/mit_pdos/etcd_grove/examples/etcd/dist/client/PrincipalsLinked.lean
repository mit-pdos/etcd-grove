/- Lean-first (no Rocq counterpart).

# The auth workload's principal calls, linked (#50 F7 S7, `notes/etcd-dist-f7.md`)

`principalCodec` over `enc`, and `remotePrincipals` (the orchestrator's side of the principal service: `Report` at
the principals' wire, `CallAll`'s goroutines) at `principalsShare`; and the principal machine's op (F7 S11):
`principalOp` over `principalClient` (`newClient`, `newUserClient` over `New_user_dist`) and `etcd_auth.Work`'s dist
proof over the auth-on interim contracts; NodeMain's auth arm (`wp_NodeMainAuth`). `RunAuth` is not linked yet.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalCodec
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remotePrincipals
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reportAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CallAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Link
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalOp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMainAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newUserClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.CallDistLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVDeleteOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TxnCommitOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchOnDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewUserDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.context.Link
public import Proof.go_uber_org.zap.NewNop
public import Proof.google_golang_org.grpc.WithNoProxy

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
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [rem_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [NaInvG GF]

/-- The principals' codec, linked over `enc`. -/
theorem wp_principalCodec : principalCodec.spec (GF := GF) (hG := hG) :=
  principalCodec.wp_proof EtcdGrove.enc.Enc.wp_Str EtcdGrove.enc.Enc.wp_Bool EtcdGrove.enc.wp_NewDec
    EtcdGrove.enc.Dec.wp_Str EtcdGrove.enc.Dec.wp_Bool EtcdGrove.enc.Dec.wp_Done

/-- **The principals' remote calls, linked** (`Report` at the principals' wire, `CallAll`'s goroutines), at
`principalsShare`. -/
theorem wp_remotePrincipals : remotePrincipals.spec (GF := GF) (hG := hG) :=
  remotePrincipals.wp_proof EtcdGrove.etcd_auth.wp_Principals
    (reportAll.wp_proof CallAll.wp_proof (fun {_ _ _ _ _ _} => EtcdGrove.remote.wp_Report))
    wp_principalCodec

end links

section links_op
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [auth_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [rem_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [NaInvG GF]

/-- `newClient`, linked (as `WatchLinked`'s). -/
theorem wp_newClientA : newClient.spec (GF := GF) (hG := hG) :=
  newClient.wp_proof zap.NewNop.wp_proof EtcdGrove.etcdstart.wp_NewClients

/-- A principal's user client, linked over `New_user_dist` (interim). -/
theorem wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG) :=
  newUserClient.wp_proof zap.NewNop.wp_proof grpc.WithNoProxy.wp_proof etcd_dist.authd.New_user_dist.wp_proof

/-- A principal's client, linked. -/
theorem wp_principalClient : principalClient.spec (GF := GF) (hG := hG) :=
  principalClient.wp_proof wp_newClientA wp_newUserClient

/-- **`Work` at the cluster view, linked** over the auth-on interim contracts (`KV_PutOn_dist`, `KV_DeleteOn_dist`,
`KV_GetOn_dist`, `Txn_CommitOn_dist`, `WatchOn_dist`) and `client_Txn_dist.law`. -/
theorem wp_Work_dist : etcd_auth.Work.spec_dist (GF := GF) (hG := hG) :=
  etcd_auth.Work.wp_proof_dist etcd_auth.wp_keyOf etcd_auth.wp_reqCtx etcd_auth.wp_refused etcd_auth.wp_checkKVs
    etcd_auth.wp_checkTxnReads etcd_auth.wp_Permitted etcd_auth.context.wp_WithTimeoutBackgroundMd
    context.wp_ErrAny etcd_auth.metadata.wp_AppendToOutgoingContext etcd_auth.v3.wp_OpPut etcd_auth.v3.wp_OpGet
    etcd_auth.v3.wp_OpTxn etcd_auth.v3.wp_Compare etcd_auth.v3.wp_Value etcd_auth.v3.wp_WithRange
    etcd_auth.v3.wp_WithPrefix etcd_auth.v3.wp_WithRev client.v3.txn.wp_If client.v3.txn.wp_Then
    client.v3.txn.wp_Else (etcd_txnlin.client_Txn_dist_law_holds client.v3.kv.wp_Txn)
    etcd_dist.authd.KV_PutOn_dist.wp_proof etcd_dist.authd.KV_DeleteOn_dist.wp_proof
    etcd_dist.authd.KV_GetOn_dist.wp_proof etcd_dist.authd.Txn_CommitOn_dist.wp_proof
    etcd_dist.authd.WatchOn_dist.wp_proof

/-- **The principal machine's op, linked** (`principalClient`, `Work`'s dist proof, `Close`). -/
theorem wp_principalOp : principalOp.spec (GF := GF) (hG := hG) :=
  principalOp.wp_proof wp_principalClient wp_Work_dist client.v3.Client.wp_Close

/-- **A principal machine, linked**: `NodeMain`'s auth arm, `remote.ServeClient` with `principalOp`. -/
theorem wp_NodeMainAuth : NodeMainAuth.spec (GF := GF) (hG := hG) :=
  NodeMainAuth.wp_proof wp_NodeCount wp_principalCodec wp_principalOp (fun {_ _} => EtcdGrove.remote.wp_ServeClient)

end links_op

end etcd_dist_client
end EtcdGrove
end Perennial
