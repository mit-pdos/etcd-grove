/-
`StartMember(name, peer, peerAddr, client, cluster, token, snapCount, catchUp, lg)`
(`examples/lib/cluster3/cluster3.go`; until 2026-11-05 package `partition`'s `startMember`, at
linkv3p's token and snapshot settings; the partition plan's S3a, 2026-10-20): one member of the
cluster of configuration `cfg` started and served -- the examples' shared `etcdstart.NewMember`
(`Spec/.../etcdstart/NewMember.lean`, whose header explains the triple) with the cluster's token,
snapshot settings, member names and URLs (`cluster3.bootPremise`, `cluster3.initURLs3`), in the
cluster's compaction mode (`cmp`), plus a listener at the member's client address (before
`Start`) and, after `Start`, etcd's gRPC server (`v3rpc.Server(s, nil, nil, opt)`) served on it. Its
success is `memberServed` (`Defs.lean`): the member's views, its thread token (`srvGoRes`), its
place in the network and etcd's KV and watch services at its client address. The premises are
`NewMember`'s plus the configuration's (`cfgOk`), the right to listen at the client address and
v3rpc's method sets (`v3rpc.Server`'s). Lean-first (no Rocq counterpart).

**The lease mode** (lease-mono3, 2026-11-06, `notes/lease-mono3-plan.md`, Scope §4 and Q2; hub step
7's E1): the member boots in the lease mode `lm` (`memberBoot`'s), and its success is
`memberServed … lm`: in a mode that grants leases, etcd's lease reads and the mode's grant and
listing registered at the client address in place of the KV calls (`kv_lease_served`'s), under the
deployment premise the lease reads' server specs take (`leasePeersOk`), only in such a mode.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcdstart (httpURL commonPremises memberBoot)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

/-- See the file header. -/
abbrev StartMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (sl₁ sl₂ sl₃ : GoSlice)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (cmp : Bool)
    (lm : lease.Mode),
  cfgOk cfg →
  -- (W4 of `notes/watch-cut-plan.md`) the members' workload, granting no lease
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir ps →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  -- (lease-mono3) the lease reads' deployment premise, in a mode that grants leases
  (lm ≠ .none → leasePeersOk) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 ∗
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗
      cluster ↦$□ GMap.insert cfg.Name3' sl₃ (GMap.insert cfg.Name2' sl₂
        (GMap.insert cfg.Name1' sl₁ ∅)) ∗
      sl₁ ↦*□ initURLs3 cfg cfg.Name1' ∗ sl₂ ↦*□ initURLs3 cfg cfg.Name2' ∗
      sl₃ ↦*□ initURLs3 cfg cfg.Name3' ∗
      bootPremise cfg N ps bootLog ctxs dir name peerAddr client id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id cmp lm ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6; 2026-11-05, hub step 7's E1, its fresh bundle) the
      -- member's WAL directory fresh (a first start), the right to listen on its peer address and
      -- to serve it with the network's raft protocol, and the right to listen on its client address
      etcdstart.memberFreshRes name ⟨some peerAddr, some client⟩ γn }}
    (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster))
      (Val #cfg.Token')) (Val #cfg.SnapCount')) (Val #cfg.SnapCatchUp')) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      (⌜err = GoInterface.nil⌝ ∗ memberServed γn s id ρ E₀ client lm) }}

end spec

end cluster3
end EtcdGrove
end Perennial
