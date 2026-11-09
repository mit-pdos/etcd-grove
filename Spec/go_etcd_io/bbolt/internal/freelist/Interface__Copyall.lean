/-
## `Interface.Copyall(dst)` (`shared.go`)

**Users.** tx_check.go:50 (`Check`); `Write` (internal).
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; the pending ids gathered and sorted (`sort.Sort`: the bound), `freePageIds()` (sorted), `Mergepgids` (`BboltCommon`).
**Changes.** new (no old spec).
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

/-- `f.Copyall(dst)`: the first `Count()` elements of `dst` become the free and pending ids, sorted (`FLState.ids`); the rest is untouched. It panics if `dst` is too short: a premise. -/
def Interface.Copyall.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (dst : GoSlice) (ds : List Pgid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ dst ↦* ds ∗ ⌜F.count ≤ ds.length ∧ F.count < flMaxIds⌝ }}
    (App (flCall fl go!"Copyall") (Val #dst))
  {{ RET #(); flOwn fl F ∗ dst ↦* (F.ids ++ ds.drop F.count) }}

end spec

end Freelist
end EtcdGrove
end Perennial
