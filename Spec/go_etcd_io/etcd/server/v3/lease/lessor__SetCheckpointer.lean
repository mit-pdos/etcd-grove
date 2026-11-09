/-
## `(*lessor).SetCheckpointer(cp)` (`lessor.go:274`): names only (an assumed spec)

**Users.** `NewServer` (`server.go:395`, 2e), with the `LeaseCheckpoint` feature on: a closure that
returns `ErrNotPrimary` unless `ensureLeadership()`, else proposes the checkpoint (`raftRequest`,
the error ignored) and returns `nil`. Concurrently with the run loop (already running) and before
any request.

**Why it is true.** `le.mu.Lock()`; `le.cp = cp`; unlock: the invariant then holds `le.cp ↦□ cp`
(frozen: `lessorCkptTok`, once) with `ckptOk cp R` (or `cp` is `nil`, which `Renew` and
`findDueScheduledCheckpoints` test). **Once**: `Renew` and the run loop test `le.cp` under the lock
and call it after releasing it (`lessor.go:412/437`, `:773/679`): a second call between could make
them call a `nil` func (a panic) or race (`nonissues/etcd-lease-setcheckpointer-once.md`). **Gated
on `R`**: the server's closure needs the server started (`ensureLeadership` reads `s.ctx`,
`s.read`, set by `start`); the lessor calls `cp` only when primary, after a `Promote`, which brings
`□ R` (`Promote.spec`).

**Changes** (from `specs-ref`, which had none: the old `NewLessor` took `ckptEffectsOk` and gave
`lessorCkptOk`): the contract is the closure's, given here; round 1: the once token and the gate.
Verify round (A9 3c F2): `ckptOk` is at `context.Background()` (the lessor's only context) with a
`threadTok` lent by the caller (`Renew`'s, the run loop's), so that the server's closure, which
calls `raftRequest`, meets it.
**Margin.** None.
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

/-- **Install the checkpointer, once**: `nil`, or one meeting `ckptOk` once `R` holds; the gate
`ckptGate le R` (what `Promote` then needs). -/
def lessor.SetCheckpointer.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (cp : GoFunc) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorCkptTok le ∗ (⌜cp = func.nil⌝ ∨ ckptOk cp R) }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"SetCheckpointer")) (Val #cp))
  {{ RET #(); ckptGate le R }}

end spec
end Lease
end EtcdGrove
end Perennial
