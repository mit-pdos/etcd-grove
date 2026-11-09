/-
## `Interface.Write(p)` (`shared.go`)

**Users.** tx.go:295 (`commitFreelist`: into the buffer `Tx.allocate` returned for `EstimatedWritePageSize()`). Snippet `ReqWriteReload`.
**Proof sketch.** the interface's contract (`Interface.<M>.contract`), proved at each dynamic type (`array.<M>.spec`, `hashMap.<M>.spec`: the method, or `shared`'s promoted one, against `flOwn`'s realization); the interface call is then the instance at `flCall` by `flOwn_dyn`; `SetFlags`, `Count()`, `SetCount`, then the ids through `unsafe.Slice` over the bytes after the header (a `[]Pgid` view of them) and `Copyall`.
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

/-- The contract of `Write` at a freelist `fl` whose method is the expression `f` (the bundle's triple; each concrete spec is its instance). `f.Write(p)`: the page becomes the freelist page of the free and pending ids, sorted (`freelistPage bs F.ids`; `freelistPage_read` reads it back). The page must have the room `EstimatedWritePageSize()` returns. -/
def Interface.Write.contract (fl : GoInterface) (f : Expr) : Prop :=
  ∀ (F : FLState) (p : Loc) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ bytesPointsto p (DFrac.own 1) bs ∗
      ⌜F.count < flMaxIds ∧ F.estimatedSize ≤ bs.length⌝ }}
    (App f (Val #p))
  {{ RET #(); flOwn fl F ∗ bytesPointsto p (DFrac.own 1) (freelistPage bs F.ids) }}

/-- `f.Write(p)`: the page becomes the freelist page of the free and pending ids, sorted (`freelistPage bs F.ids`; `freelistPage_read` reads it back). The page must have the room `EstimatedWritePageSize()` returns. Through the interface (`flCall`): proved from `array.Write.spec`, `hashMap.Write.spec` and `flOwn_dyn`/`flReaders_dyn` (Perennial's `method_interface_ok` steps the call to the dynamic type's method). -/
def Interface.Write.spec : Prop := ∀ fl, Interface.Write.contract (GF := GF) fl (flCall fl go!"Write")

end spec

end Freelist
end EtcdGrove
end Perennial
