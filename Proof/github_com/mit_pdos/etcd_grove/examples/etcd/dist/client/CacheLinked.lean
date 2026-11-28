/- Lean-first (no Rocq counterpart).

# The cache workload's orchestrator, linked (#50 F6, `notes/etcd-dist-plan.md` §29)

`RunCache.wp_proof` at its linked callees: the cache library's (`go_etcd_io/etcd/cache/v3/Link.lean`), the cache
example's helpers' dist copies, etcdstart's, clientv3's option constructors, `context` and `time`, the client's
linked `client.v3.kv.wp_Get` (at the client's `isKv` of the auth-off view, stage B′), the interim axioms `Watch_dist` and
`RequestProgress_dist`, and the writers (`remoteWriters.wp_proof`, N10a's, over `reportAll`, `CallAll`,
`lib/remote`'s `Report`, `writerAttempt` and the writers' codec: `WatchLinked.wp_remoteWriters`, the watch
workload's). No hypothesis.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunCache
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.GenAllR
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remoteWriters
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reportAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CallAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerAttempt
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.cacheCollect
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.awaitProgress
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkProgress
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.lastVal
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.hasKey
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkGet
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_etcd_io.etcd.cache.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.WithPrefix
public import Proof.go_etcd_io.etcd.client.v3.getPrefix
public import Proof.go_etcd_io.etcd.client.v3.WithRev
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net
open etcd_dist

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [NaInvG GF]

/-- **The cache workload's orchestrator, linked** (the writers' calls as the watch workload's,
`WatchLinked.wp_remoteWriters`, over N10a's linked `writerCodec`). -/
theorem wp_RunCache : RunCache.spec (GF := GF) (hG := hG) :=
  RunCache.wp_proof (GenAll_receipts.wp_proof EtcdGrove.etcdstart.wp_Gen) (newClient.wp_proof zap.NewNop.wp_proof etcdstart.wp_NewClients)
    ended.wp_proof checked.wp_proof client.v3.kv.wp_Get Watch_dist.wp_proof RequestProgress_dist.wp_proof
    context.wp_ErrAny context.WithTimeoutBackground.wp_proof (WithPrefix.wp_proof getPrefix.wp_proof) WithRev.wp_proof
    wp_New Cache.wp_Watch Cache.wp_RequestProgress Cache.wp_Get Cache.wp_Close
    wp_remoteWriters
    _root_.Perennial.time.wp_AfterFunc _root_.Perennial.time.Timer.wp_Stop etcdstart.wp_MaxRev
    cacheCollect.wp_proof (awaitProgress.wp_proof client.v3.WatchResponse.wp_IsProgressNotify)
    checkProgress.wp_proof etcdstart.wp_Check (checkGet.wp_proof lastVal.wp_proof hasKey.wp_proof)

end linked

end etcd_dist_client
end EtcdGrove
end Perennial
