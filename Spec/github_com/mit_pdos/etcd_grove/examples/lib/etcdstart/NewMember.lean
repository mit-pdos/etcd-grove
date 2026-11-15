/-
`NewMember(name, peer, peerAddr, client, cluster, token, snapCount, catchUp, lg)` (`examples/lib/etcdstart/common.go`;
2026-10-22, D33): member `name` of a new cluster built and its raft handler served -- `newServer`,
`net.Listen` at the peer address, `go http.Serve(l, s.RaftHandler())`; what putget3's, linkv3's and
linkv3p's `startMember`s did before `Start`. Lean-first (no Rocq counterpart).

**The triple:** `newServer`'s (any snapshot settings; either compaction mode `cmp` with the
auto-compactor off, since 2026-11-05), its fresh bundle with the peer address (`memberFreshRes`, hub
step 7: also the right to listen on the peer address and to serve it with the network's raft
protocol) and, for `http.Serve`, `http://peerAddr` one of the member's peer URLs in the directory:
an error, or the member built (`memberBuilt`).
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
abbrev NewMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client token : GoString)
    (snapCount catchUp : w64) (peer : GoSlice) (cluster lg : Loc) (M : GMap GoString GoSlice)
    (iu : GoString → List _root_.Perennial.net.url.URL) (Uok : BootURLs → Prop)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (id : w64) (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (cmp : Bool)
    (lm : lease.Mode),
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
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      -- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      -- (2026-11-02, the backend-auth-split stage) the thread's token, `NewServer`'s, given back
      threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗ cluster ↦$□ M ∗ ([∗map] k ↦ sl ∈ M, sl ↦*□ iu k) ∗
      bootPremise N ps bootLog ctxs dir token name Uok id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id cmp lm ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6; 2026-11-05, hub step 7, its fresh bundle) the
      -- member's WAL directory fresh (a first start), the right to listen on its peer address and
      -- to serve it with the network's raft protocol
      memberFreshRes name ⟨some peerAddr, none⟩ γn }}
    (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #token))
      (Val #snapCount)) (Val #catchUp)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗ memberBuilt s ρ E₀ lg γn id N true (m := lm)) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
