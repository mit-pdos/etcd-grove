/-
`(*lessor).runLoop()` (`server/lease/lessor.go:618-636`), the expiry loop `newLessor` forks. Lean-first;
prove-ps2-newlessor3, 2026-11-21.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.runLoop()`, on its own goroutine, with a reader slot of `le.mu`, the notifier cell's token,
the level-0 token and `doneC`'s close right: every 500 ms (a ticker) `revokeExpiredLeases` and
`checkpointScheduledLeases`, until `stopC` is closed; then it stops the ticker and closes `doneC`
(deferred), and gives the level-0 token back (prove-ps2-newlessor5, 2026-11-21: until then `True`;
the forked goroutine ends with its thread token, `wp_fork_tok_body`, whose level-0 token it gave). -/
abbrev lease.lessor.runLoop.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (GA : w64 → IProp GF) (ri : _root_.Perennial.time.Duration)
    (d : GoChan) (γd : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorCfg lp ∗ lessorExpiredC lp GA ∗ lessorGuard γl GA ∗ lessorStopRecv lp ∗
      lF go!"expiredLeaseRetryInterval" lp ↦□ ri ∗ lF go!"doneC" lp ↦□ d ∗
      ownBroadcastChan d γd iprop(True) .Pending ∗
      lessorRd lp γl ∗ notifRTok γl ∗ levelTok leaseLvl ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"runLoop")) (Val #()))
  {{ RET #(); levelTok leaseLvl }}

end spec

end EtcdGrove
end Perennial
