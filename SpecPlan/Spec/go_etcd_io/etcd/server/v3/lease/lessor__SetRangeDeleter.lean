/-
## `(*lessor).SetRangeDeleter(rd)` (`lessor.go:267`)

**Users.** mvcc (3e) at construction, through the `Lessor` interface: `NewStore`
(`kvstore.go:117`: the store's `Write`), `newWatchableStore` (`watchable_store.go:107`: the
watchable store's, so revocations notify watchers), on the thread that builds the store (bootstrap,
holding the writer's token). Snippet `lessor.go` (`ReqRevokeDeletes`).

**Proof sketch.** `le.mu.Lock()`; `le.rd = rd` (both halves of the field: the invariant's and the
writer's token's); the history appended (`n + 1`); unlock.

**Changes** (from `specs-ref`'s `lessor__SetRangeDeleter.lean`, `rdOwn γl rd0` and mvcc's `rdIs`):
the deleter is a field of the writer's state; its contract (`rdOk`) is the caller's, given at
`Revoke`. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Api

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

/-- **Install the range deleter** (the writer). -/
def lessor.SetRangeDeleter.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (n : Nat) (ls : LessorState) (rd : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorState γ n ls }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"SetRangeDeleter")) (Val #rd))
  {{ RET #(); lessorState γ (n + 1) { ls with rd := rd } }}

end spec
end Lease
end EtcdGrove
end Perennial
