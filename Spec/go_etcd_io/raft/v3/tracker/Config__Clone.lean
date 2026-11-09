/-
## `Config.Clone()`

**Users.** `getStatus` (`status.go:74`: `Status.Config`, R1's `statusOwn`, the client's to keep),
confchange's `checkAndCopy` (`confchange.go:283`). Snippet `raftconf/tracker.go` (`ReqCloneFresh`).

**Proof sketch.** Four `clone`s of the maps (`nil` stays `nil`, a map is copied by `range` into a
fresh one), the `Config` literal. The literal leaves `AutoLeave` out, so the copy has it `false`
(`issues/raft-config-clone-autoleave.md`, `specs-ref`: `Status().Config.AutoLeave` is wrong in a
joint configuration entered with auto-leave); `{m with autoLeave := false}` is still valid and in
canonical form.

**Changes** (from `specs-ref`'s `tracker/Config__Clone.lean`): over `configOwn` (was `ownCfgCC`).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.tracker.Assumptions]

/-- A fresh copy of the configuration, without its auto-leave flag. -/
def Config.Clone.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (cfg : go_etcd_io.raft.v3.tracker.Config) (dq : DFrac)
    (m : Membership),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ p ↦{dqp} cfg ∗ configOwn cfg dq m }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Config.ty @!! go!"Clone")) (Val #()))
  {{ (cfg' : go_etcd_io.raft.v3.tracker.Config), RET #cfg'; p ↦{dqp} cfg ∗ configOwn cfg dq m ∗
      configOwn cfg' (DFrac.own 1) { m with autoLeave := false } }}

end spec
end Tracker
end EtcdGrove
end Perennial
