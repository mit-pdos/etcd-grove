/-
`StartServer(name, peerAddr, clientAddr, lg)` (`examples/lib/etcdstart/common.go`; 2026-10-22, D33): the one
member of a new cluster started -- its peer URL slice, `newServer` (with the cluster's map
`{name ↦ peer}` and the token `name`), `s.Start()`; what putget's, linkv's, linkvtxn's, watchkv's
and cachekv's `Main`s did up to `Start`. Lean-first (no Rocq counterpart).

**The triple:** given the member's ghost state (`memberBoot`, `alloc1`'s) and the network's HTTP side (`netHttpOk`), a thread
token (`Start` forks the server's goroutines; it comes back in `srvGoRes`), `bootstrap`'s contract
for it (`bootPremise` at the one-member cluster `[id]`, the token `name` and the URLs `urls1`) and
the premises the members share: an error with the thread token, or the server started
(`memberUp`).

**The pure premises:** `newServer`'s at the one-member cluster.
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
abbrev StartServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString) (lg : Loc)
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
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      -- (sweep repairs 1, R1-2) the logger a zap logger (until then `lg ≠ null`)
      zapLoggerOk lg ∗
      threadTok ∗
      bootPremise N [id] bootLog ctxs dir name name (urls1 name peerAddr client) id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot γ ctxs ρ E₀ Φs id (m := lm) ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6; 2026-11-05, hub step 7, its start bundle) the
      -- member's WAL directory fresh: a first start
      memberFreshRes name {} γn }}
    (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer))
      (Val #name)) (Val #peerAddr)) (Val #client)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ memberUp s ρ E₀ lg γn id lm ∗ leaseTTLRowR s [id]) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
