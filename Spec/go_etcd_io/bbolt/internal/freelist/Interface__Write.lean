/-
## `Interface.Write(p)` (`shared.go`)

**Users.** tx.go:295 (`commitFreelist`: into the buffer `Tx.allocate` returned for `EstimatedWritePageSize()`). Snippets `ReqWriteReload`, `ReqEstimate`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; `SetFlags`, `Count()`, `SetCount`, then the ids through `unsafe.Slice` over the bytes after the header (a `[]Pgid` view of them) and `Copyall`.
**Changes.** from `specs-ref`'s `Interface__Write.lean`: the page as its bytes (`freelistPage`) and any bytes after the header (not only zeroed ones); the room as `estimatedSize`.
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

/-- `f.Write(p)`: the page becomes the freelist page of the free and pending ids, sorted (`freelistPage bs F.ids`; `freelistPage_read` reads it back). The page must have the room `EstimatedWritePageSize()` returns. -/
def Interface.Write.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (p : Loc) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ bytesPointsto p (DFrac.own 1) bs ∗
      ⌜F.count < flMaxIds ∧ F.estimatedSize ≤ bs.length⌝ }}
    (App (flCall fl go!"Write") (Val #p))
  {{ RET #(); flOwn fl F ∗ bytesPointsto p (DFrac.own 1) (freelistPage bs F.ids) }}

end spec

end Freelist
end EtcdGrove
end Perennial
