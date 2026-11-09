/-
## `Interface.EstimatedWritePageSize()` (`shared.go`, `array.go`, `hashmap.go`)

**Users.** tx.go:289 (`commitFreelist`: the pages to allocate for `Write`), tx.go:361 (stats). Snippet `ReqEstimate`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; `Count()`, then `16 + 8 * (n + 1 if n ≥ 0xFFFF)`, below `2^63` by the bound.
**Changes.** from `specs-ref`'s `Interface__EstimatedWritePageSize.lean`: over `FLState`; the bound `flMaxIds` (a named constant) in place of `WF`'s `2^63`.
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

/-- `f.EstimatedWritePageSize()`: the bytes `Write` needs (`FLState.estimatedSize`). -/
def Interface.EstimatedWritePageSize.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ ⌜F.count < flMaxIds⌝ }}
    (App (flCall fl go!"EstimatedWritePageSize") (Val #()))
  {{ RET #(W64 (F.estimatedSize : Int)); flOwn fl F }}

end spec

end Freelist
end EtcdGrove
end Perennial
