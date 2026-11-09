/-
## `Progress.SentEntries(n, bytes)`

**Users.** `maybeSendAppend` (`raft.go:659`, after `IsPaused()` was false, so not in snapshot
state; entries only to a replicating peer whose ring is not full, `raft.go:639`): R2.

**Proof sketch.** In replicate: `Next += n` and `Inflights.Add` (not full: premise) if `n > 0`; the
pause is `Full()`. In probe: paused if `n > 0`. In snapshot state Go panics ("sending append in
unhandled state"): premise.

**Changes** (from `specs-ref`'s `tracker/Progress__SentEntries.lean`): over the model.

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

/-- Accounts for an append of `n` entries (`bytes` of payload) sent to the peer. -/
def Progress.SentEntries.spec : Prop :=
  ∀ (p : Loc) (P : ProgressV) (n bytes : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ progressOwn p P ∗
      ⌜P.state ≠ .snapshot ∧ (P.state = .replicate → 0 < sint.Z n → P.ins.full = false)⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.Progress.ty @!! go!"SentEntries")) (Val #n)) (Val #bytes))
  {{ RET #(); progressOwn p (P.sentEntries n bytes) }}

end spec
end Tracker
end EtcdGrove
end Perennial
