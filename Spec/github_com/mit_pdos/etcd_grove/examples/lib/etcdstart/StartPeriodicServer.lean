/-
`StartPeriodicServer(name, peerAddr, clientAddr, period, lg)` (`examples/lib/etcdstart/etcdstart.go`;
periodic mode, 2026-11-02): `StartServer` with the auto-compactor on, in periodic mode, keeping the
revisions of the last `period` -- `newServerMode` in periodic mode at that period, `s.Start()`;
`putgetc`'s start. Lean-first (no Rocq counterpart).

**The triple:** the compacting start's (`Spec/.../common/StartCompactingServer.lean`).

**The pure premises:** `StartServer`'s, the period at least 10ns (`v3compactor.New`'s premise: a
shorter one busy-loops) and the cluster's retention `0` (`NewServer`'s premise in periodic mode).
-/
module

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
abbrev StartPeriodicServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString) (period : w64)
    (lg : Loc)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString) (id : w64)
    (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
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
  lg ≠ null → 10 ≤ sint.Z period → ρ.rd.kv.cret = 0 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      threadTok ∗
      -- (M2's item 15, stage B3) at `N` write tokens (`N + N` from M2 until then: `N` more, the
      -- compaction's write-back stock)
      bootPremise N [id] bootLog ctxs dir name name (urls1 name peerAddr client) id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      -- (M2, the storage side, N1) the member's boot bundle in compaction mode
      memberBoot γ ctxs ρ E₀ Φs id true ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id ∗
      -- (2026-11-03, the WAL's API, change 6) the member's WAL directory fresh: a first start
      walDirFresh (config.walDirOf (name ++ go!".etcd") go!"") }}
    (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartPeriodicServer))
      (Val #name)) (Val #peerAddr)) (Val #client)) (Val #period)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨ (⌜err = GoInterface.nil⌝ ∗ memberUp s ρ E₀ lg γn id) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
