/-
`newServerMode(name, peer, client, cluster, token, mode, retention, snapCount, catchUp, lg)`
(`examples/lib/etcdstart/common.go`; periodic mode, 2026-11-02): `newServer` with the auto-compactor's mode
a parameter -- member `name` of a new cluster with token `token` built, its configuration and
`etcdserver.NewServer`. Lean-first (no Rocq counterpart).

**The triple:** `newServer`'s (`Spec/.../common/newServer.lean`), in the compaction mode `cmp`, with the
auto-compactor's configuration by the compactor's slot (`v3compactor.bootCfg`, `NewServer`'s
premise: off in either mode, the retention zero; or on in compaction mode, in revision mode at a
positive retention of at least the cluster's, or in periodic mode at a period of at least 10ns and a
cluster retention of `0`); at `N` write tokens (`N + N` on until M2's item 15, stage B3), on with the boot bundle in
compaction mode (`memberBoot … true`).
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
abbrev newServerMode.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token mode : GoString)
    (retention snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (cmp : Bool) (lm : lease.Mode),
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  γ.vs = ps → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  -- (2026-11-03, the final whole-`bootOk` review's M2) the directory names the peers
  rafthttp.bootCfg dir ps →
  Uok ⟨[httpURL peerAddr], [httpURL client], M, iu⟩ →
  -- (2026-11-02, the backend-auth-split stage, Q8) the initial cluster's names valid UTF-8,
  -- `bootPremise`'s condition
  (∀ k, (M.lookup k).isSome → utf8Valid k) →
  -- the compactor's slot (`v3compactor.bootCfg`, `NewServer`'s premise; K1 of
  -- `notes/k8s-compactor-plan.md`): off in either compaction mode, or on in compaction mode
  v3compactor.bootCfg mode retention cmp ρ.rd.kv.cret →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      -- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      -- (2026-11-02, the backend-auth-split stage) the thread's token, `NewServer`'s, given back
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      -- at `N` write tokens in both modes (M2's item 15, stage B3; until then `N + N` on, `N` more
      -- for the compaction's write-back stock)
      bootPremise N ps bootLog ctxs dir token name Uok id ∗
      commonPremises ∗ context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id cmp lm ∗
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6; 2026-11-05, hub step 7, its start bundle) the
      -- member's WAL directory fresh: a first start
      memberFreshRes name {} γn }}
    (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.newServerMode))
      (Val #name)) (Val #peer)) (Val #client)) (Val #cluster)) (Val #token)) (Val #mode))
      (Val #retention)) (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ memberBuilt s ρ E₀ lg γn id N false (m := lm) ∗
          leaseTTLRowR s ps ∗
          -- (R2c-5) the data directory, the name's `.etcd`, with no dedicated WAL directory
          -- (`srvDataDir`, the slot's: `srvStop.dataDir`), which a stop request carries
          srvDataDir s (name ++ go!".etcd")) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
