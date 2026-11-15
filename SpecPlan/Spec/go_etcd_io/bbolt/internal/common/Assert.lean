/-
## `Assert(cond, msg, v...)` (`internal/common/verify.go`)

**Users.** 19 call sites in bbolt (tx.go:185,304 managed transactions, db.go:1198 mapped, node.go:141,180, inode.go, ...): each a condition its caller's proof shows.
**Proof sketch.** `if !cond { panic(fmt.Sprintf(...)) }`.
**Changes.** from `specs-ref`'s file of the same name: the condition a premise instead of the literal `true` (the same statement, readable at a variable condition).
**Margin.** none: the post is what the code computes.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `Assert(cond, msg, v...)` returns when `cond` holds; it panics otherwise, which the premise excludes. -/
def Assert.spec : Prop :=
  ∀ (cond : Bool) (msg : GoString) (vs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ ⌜cond = true⌝ }}
    (App (App (App (Val (@! go_etcd_io.bbolt.internal.common.Assert)) (Val #cond)) (Val #msg)) (Val #vs))
  {{ RET #(); True }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
