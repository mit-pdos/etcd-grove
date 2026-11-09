/-
## `(*lessor).SetCheckpointer(cp)` (`lessor.go:274`): names only (an assumed spec)

**Users.** `NewServer` (`server.go:395`, 2e), with the `LeaseCheckpoint` feature on: a closure that
returns `ErrNotPrimary` unless `ensureLeadership()`, else proposes the checkpoint (`raftRequest`,
the error ignored) and returns `nil`. Concurrently with the run loop (already running) and before
any request.

**Why it is true.** `le.mu.Lock()`; `le.cp = cp`; unlock: the invariant then holds `ckptOk cp` of
the new value (or `cp` is `nil`, which `Renew` and `findDueScheduledCheckpoints` test).

**Changes** (from `specs-ref`, which had none: the old `NewLessor` took `ckptEffectsOk` and gave
`lessorCkptOk`): the contract is the closure's, given here. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Install the checkpointer** (any goroutine): `nil`, or one meeting `ckptOk`. -/
def lessor.SetCheckpointer.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (cp : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      (⌜cp = func.nil⌝ ∨ ckptOk cp) }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"SetCheckpointer")) (Val #cp))
  {{ RET #(); True }}

end spec
end Lease
end EtcdGrove
end Perennial
