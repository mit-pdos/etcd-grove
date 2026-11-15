/-
## `NewArrayFreelist()` (`internal/freelist/array.go`)

**Users.** db.go:1387-1392 (`newFreelist`, by `Options.FreelistType`), called by `loadFreelist` (db.go:454). Snippet `ReqAllocFree`.
**Proof sketch.** `newShared()` (three `make`s), the `array` struct, the embedded `Interface` set to itself; the realization of `flOwn` at the empty state, `flReaders` at `nil`.
**Changes.** new (no old spec: the old proofs started from `Open`'s freelist).
**Margin.** none: the post is what the code computes.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.internal.freelist.Api

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

/-- `NewArrayFreelist()`: a new, empty freelist, as an interface value of dynamic type `*array`: no free, pending or allocated page, no reader. -/
def NewArrayFreelist.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist }}
    (App (Val (@! go_etcd_io.bbolt.internal.freelist.NewArrayFreelist)) (Val #()))
  {{ (l : Loc), RET #(arrayIface l);
      flOwn (arrayIface l) FLState.empty ∗
      flReaders (arrayIface l) [] }}

end spec

end Freelist
end EtcdGrove
end Perennial
