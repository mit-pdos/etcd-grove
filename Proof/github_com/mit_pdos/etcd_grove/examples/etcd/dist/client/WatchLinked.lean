/- Lean-first (no Rocq counterpart).

# The watch workload across machines, linked (#50 N10a, `notes/etcd-dist-plan.md` §24)

`RunWatch` (the orchestrator; its writers' Puts by `GenAll_receipts`) and `NodeMain`'s watch arm (a writer machine) with every callee's proof:
the interim contracts at clientv3's interface across machines, `Watch_dist` (N3, `WatchDist.lean`;
linked here first, after the watcher-environment refactor, §25) and `KV_Put_dist` (N2); the writers'
calls over `lib/remote` (`Report`, `ServeClient`) at the writers' wire (§28); `etcdstart`'s, clientv3's
and Perennial's linked results.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.GenAllR
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerOp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.NodeMainWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerAttempt
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerCodec
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remoteWriters
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reportAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CallAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Rotate
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.WithPrefix
public import Proof.go_etcd_io.etcd.client.v3.getPrefix
public import Proof.go_etcd_io.etcd.client.v3.WithRev
public import Proof.go_etcd_io.etcd.client.v3.WithProgressNotify
public import Proof.go_etcd_io.etcd.client.v3.WithCreatedNotify
public import Proof.context.WithTimeoutBackground
public import Proof.context.Link
public import Proof.go_uber_org.zap.NewNop
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Perennial.Proof.time.Link

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
variable [etcdstart_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [dial : go_etcd_io.etcd.client.v3.DialWithBalancerBody]
variable [rem_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [NaInvG GF]

/-- `newClient`, linked. -/
theorem wp_newClient : newClient.spec (GF := GF) (hG := hG) :=
  newClient.wp_proof zap.NewNop.wp_proof EtcdGrove.etcdstart.wp_NewClients

/-- A writer machine's call, linked: `Writer` across machines over `KV_Put_dist` (N2's interim
contract). -/
theorem wp_writerOp : writerOp.spec (GF := GF) (hG := hG) :=
  writerOp.wp_proof (Writer_dist.wp_proof EtcdGrove.etcdstart.context.wp_WithTimeoutBackground EtcdGrove.context.wp_ErrAny
    KV_Put_dist.wp_proof)

/-- The writers' codec, linked over `enc`. -/
theorem wp_writerCodec : writerCodec.spec (GF := GF) (hG := hG) :=
  writerCodec.wp_proof EtcdGrove.enc.Enc.wp_Int EtcdGrove.enc.Enc.wp_Str EtcdGrove.enc.Enc.wp_I64
    EtcdGrove.enc.wp_NewDec EtcdGrove.enc.Dec.wp_Int EtcdGrove.enc.Dec.wp_Str EtcdGrove.enc.Dec.wp_I64
    EtcdGrove.enc.Dec.wp_Done

/-- The writers' remote calls, linked (`Report` at the writers' wire, `CallAll`'s goroutines). -/
theorem wp_remoteWriters : remoteWriters.spec (GF := GF) (hG := hG) :=
  remoteWriters.wp_proof (reportAll.wp_proof CallAll.wp_proof (fun {_ _ _ _ _ _} => EtcdGrove.remote.wp_Report))
    wp_writerCodec writerAttempt.wp_proof

/-- **The watch workload's orchestrator, linked**: over `Watch_dist` (N3's interim contract) and the
writers' calls. -/
theorem wp_RunWatch : RunWatch.spec (GF := GF) (hG := hG) :=
  RunWatch.wp_proof (GenAll_receipts.wp_proof EtcdGrove.etcdstart.wp_Gen) wp_newClient ended.wp_proof checked.wp_proof
    Watch_dist.wp_proof (WithPrefix.wp_proof getPrefix.wp_proof) WithRev.wp_proof
    WithProgressNotify.wp_proof WithCreatedNotify.wp_proof
    wp_remoteWriters time.wp_AfterFunc time.Timer.wp_Stop EtcdGrove.etcdstart.wp_MaxRev
    EtcdGrove.etcdstart.wp_Collect EtcdGrove.etcdstart.wp_Check

/-- **A watch writer machine, linked**: `NodeMain`'s watch arm, its calls `writerOp` over `KV_Put_dist`. -/
theorem wp_NodeMainWatch : NodeMainWatch.spec (GF := GF) (hG := hG) :=
  NodeMainWatch.wp_proof wp_NodeCount Rotate.wp_proof wp_newClient wp_writerCodec writerAttempt.wp_proof
    wp_writerOp (fun {_ _} => EtcdGrove.remote.wp_ServeClient)


end links

end etcd_dist_client
end EtcdGrove
end Perennial
