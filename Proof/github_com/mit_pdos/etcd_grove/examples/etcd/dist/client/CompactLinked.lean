/-
**The compact workload of `examples/etcd/dist/client`, linked** (#50 F5, `notes/etcd-dist-plan.md` §26):
`RunCompact.wp_proof` and `checkCompactRev.wp_proof` at their callees' linked results, the cross-machine
clientv3 calls at the interim axioms `etcd_dist.KV_Put_dist.wp_proof`, `KV_Get_dist.wp_proof`,
`KV_Compact_dist.wp_proof` (N2's, reviewed: `notes/axiom-review/n2-kv-dist.md`) and
`etcd_dist.Watch_dist.wp_proof` (N3's, reviewed: `notes/axiom-review/n3-watch-dist.md`, and under the
watcher-environment refactor `notes/axiom-review/wenv-isnewclient.md`); `Client.Close` at its existing
trust-boundary axiom. The first result resting on `Watch_dist`: `Serve_dist`'s docstring names the watch
streams (the N3 review's F4) in the same commit. No new axiom. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunCompact
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkCompactRev
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVCompactDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_uber_org.zap.NewNop
public import Perennial.Proof.context.Link
public import Proof.context.Link
public import Proof.context.WithTimeoutBackground
public import Proof.context.WithTimeoutBackgroundMd
public import Proof.strconv.Itoa
public import Proof.go_etcd_io.etcd.client.v3.WithRev
public import Proof.go_etcd_io.etcd.client.v3.Client__Close
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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **compact's `checkCompactRev`, linked.** -/
theorem wp_checkCompactRev : checkCompactRev.spec (GF := GF) (hG := hG) :=
  checkCompactRev.wp_proof context.wp_Background context.WithTimeoutBackground.wp_proof
    context.WithTimeoutBackgroundMd.wp_proof context.wp_ErrAny WithRev.wp_proof Watch_dist.wp_proof
    etcdstart.wp_CompactRev KV_Get_dist.wp_proof

/-- **compact's orchestrator, linked.** -/
theorem wp_RunCompact : RunCompact.spec (GF := GF) (hG := hG) :=
  RunCompact.wp_proof (newClient.wp_proof zap.NewNop.wp_proof etcdstart.wp_NewClients)
    checked.wp_proof ended.wp_proof wp_checkCompactRev EtcdGrove.strconv.Itoa.wp_proof
    context.wp_Background context.WithTimeoutBackground.wp_proof context.wp_ErrAny
    EtcdGrove.Client.Close.wp_proof WithRev.wp_proof _root_.Perennial.time.wp_AfterFunc
    _root_.Perennial.time.Timer.wp_Stop etcdstart.wp_Collect KV_Put_dist.wp_proof KV_Get_dist.wp_proof
    KV_Compact_dist.wp_proof Watch_dist.wp_proof

end linked

end etcd_dist_client
end EtcdGrove
end Perennial
