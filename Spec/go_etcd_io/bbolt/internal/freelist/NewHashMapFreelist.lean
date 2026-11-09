/-
## `NewHashMapFreelist()` (`internal/freelist/hashmap.go`)

**Users.** db.go:1387-1392 (`newFreelist`, by `Options.FreelistType`), called by `loadFreelist` (db.go:454). Snippet `ReqAllocFree`.
**Proof sketch.** `newShared()` (three `make`s), the `hashMap` struct, the embedded `Interface` set to itself; the realization of `flOwn` at the empty state, `flReaders` at `nil`.
**Changes.** new (no old spec: the old proofs started from `Open`'s freelist).
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

/-- `NewHashMapFreelist()`: a new, empty freelist as an interface value: no free, pending or allocated page, no reader. -/
def NewHashMapFreelist.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist }}
    (App (Val (@! go_etcd_io.bbolt.internal.freelist.NewHashMapFreelist)) (Val #()))
  {{ (fl : GoInterface), RET #fl; flOwn fl FLState.empty ∗ flReaders fl [] }}

end spec

end Freelist
end EtcdGrove
end Perennial
