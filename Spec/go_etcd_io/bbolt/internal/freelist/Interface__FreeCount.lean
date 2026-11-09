/-
## `Interface.FreeCount()` (`shared.go`, `array.go`, `hashmap.go`)

**Users.** tx.go:359 (stats), db.go:467 (`loadFreelist`'s stats).
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; the counts are sums of lengths (an `int`: the bound).
**Changes.** from `specs-ref`'s `Interface__FreeCount.lean`: over `FLState`; the bound `flMaxIds` (a named constant) in place of `WF`'s `2^63`.
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Freelist

open Iris Iris.BI go_etcd_io.bbolt.internal.common BboltCommon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.FreeCount()`: the number of free pages. -/
def Interface.FreeCount.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ ⌜F.count < flMaxIds⌝ }}
    (App (flCall fl go!"FreeCount") (Val #()))
  {{ RET #(W64 (F.free.domList.length : Int)); flOwn fl F }}

end spec

end Freelist
end EtcdGrove
end Perennial
