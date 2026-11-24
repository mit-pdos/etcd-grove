/-
`(*lessor).revokeExpiredLeases()` (`server/lease/lessor.go:638-663`). Lean-first (no Rocq
counterpart); prove-ps2-newlessor3, 2026-11-21.
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

/-- `le.revokeExpiredLeases()`, the expiry loop's (its reader slot, its token of the notifier's
cell, the level-0 token): under the read lock, if primary, the expired leases of the map
(`findExpiredLeases`); if any, sent on `expiredC` unless the receiver is busy or the lessor stops
(`select` with a `default`). Each slice sent meets `expiredC`'s predicate (`lessorExpiredC lp GA`). -/
abbrev lease.lessor.revokeExpiredLeases.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (GA : w64 → IProp GF) (ri : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorCfg lp ∗ lessorExpiredC lp GA ∗ lessorGuard γl GA ∗
      lF go!"expiredLeaseRetryInterval" lp ↦□ ri ∗ lessorRd lp γl ∗ notifRTok γl ∗
      levelTok leaseLvl ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"revokeExpiredLeases")) (Val #()))
  {{ RET #(); lessorRd lp γl ∗ notifRTok γl ∗ levelTok leaseLvl }}

end spec

end EtcdGrove
end Perennial
