/-
`StartCompactingServer(name, peerAddr, clientAddr, retention, lg)` (`examples/lib/etcdstart/common.go`;
M2, 2026-10-27, `notes/m2-plan.md`): `StartServer` with the auto-compactor on, in revision mode,
keeping `retention` revisions -- `newServer` with that retention, `s.Start()`; `putgetc`'s start.
Lean-first (no Rocq counterpart).

**The triple:** `StartServer`'s.

**The pure premises:** `StartServer`'s, and the retention positive or `0` (revision mode; at `0`
etcd's own compactor is off and the cluster compacts only at its clients' requests, Kubernetes'
deployment, `examples/k8s/compactor`: K3 of `notes/k8s-compactor-plan.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- See the file header. -/
abbrev StartCompactingServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString) (retention : w64)
    (lg : Loc)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString) (id : w64)
    (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (lm : lease.Mode),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = [id] → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir [id] →
  -- (2026-11-02, the backend-auth-split stage, Q8) the member's name valid UTF-8, `bootPremise`'s
  -- condition on the initial cluster's names
  utf8Valid name →
  -- (K3 of the k8s compactor plan, 2026-11-04) the retention positive, or `0`: etcd's compactor
  -- off, every compaction a client's (Kubernetes' deployment; `v3compactor.bootCfg`'s off case)
  0 ≤ sint.Z retention →
  -- (C3's server stage, 2026-11-02) the cluster's retention at most the compactor's
  (ρ.rd.kv.cret : Int) ≤ sint.Z retention →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      -- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      threadTok ∗
      -- (M2's item 15, stage B3) at `N` write tokens (`N + N` from M2 until then: `N` more, the
      -- compaction's write-back stock)
      bootPremise N [id] bootLog ctxs dir name name (urls1 name peerAddr client) id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      -- (M2, the storage side, N1) the member's boot bundle in compaction mode
      memberBoot γ ctxs ρ E₀ Φs id true lm ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6; 2026-11-05, hub step 7, its start bundle) the
      -- member's WAL directory fresh: a first start
      memberFreshRes name {} γn }}
    (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartCompactingServer))
      (Val #name)) (Val #peerAddr)) (Val #client)) (Val #retention)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨ (⌜err = GoInterface.nil⌝ ∗ memberUp s ρ E₀ lg γn id lm) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
