/-
`StartCompactingServer(name, peerAddr, clientAddr, retention, lg)` (`examples/common/common.go`;
M2, 2026-10-27, `notes/m2-plan.md`): `StartServer` with the auto-compactor on, in revision mode,
keeping `retention` revisions -- `newServer` with that retention, `s.Start()`; `putgetc`'s start.
Lean-first (no Rocq counterpart).

**The triple:** `StartServer`'s.

**The pure premises:** `StartServer`'s, and the retention positive (phase 0's scope: revision
mode, a positive retention).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev StartCompactingServer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString) (retention : w64)
    (lg : Loc)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString) (id : w64)
    (γ : SrvRaft) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.vs = [id] → γ.rule = srvRule (W64 0) bootLog → γ.boot = bootLog → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ → γn.dir = dir → netDirOk dir → go!"http://" ++ peerAddr ∈ dir id →
  lg ≠ null → 0 < sint.Z retention →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → storage.dbOpensOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      threadTok ∗
      -- (M2, 2026-10-31) at `N + N` write tokens: `N` more, the compaction's write-back stock
      bootPremise (N + N) [id] bootLog ctxs dir name name (urls1 name peerAddr client) id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      -- (M2, the storage side, N1) the member's boot bundle in compaction mode
      memberBoot γ ctxs ρ E₀ Φs id true ∗
      -- (2026-10-24, rafthttp stage 6d; until then the member's network slot) the network's HTTP
      -- side for it
      netHttpOk γn id }}
    (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.common.StartCompactingServer))
      (Val #name)) (Val #peerAddr)) (Val #client)) (Val #retention)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨ (⌜err = GoInterface.nil⌝ ∗ memberUp s ρ E₀ lg γn id) }}

end spec

end common
end EtcdGrove
end Perennial
