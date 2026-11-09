/-
## `Interface.NoSyncReload(ids)` (`shared.go`)

**Users.** tx.go:343 (`rollback` without a synced freelist: `db.freepages()`, the pages no committed tree reaches); `Reload` (internal). Snippet `ReqRollback`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; a map of the pending ids, the ids filtered into a new slice, `Init` (sorted, so the hash map's check passes).
**Changes.** from `specs-ref`'s `Interface__NoSyncReload.lean`: over `FLState`; the slice is only read.
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

/-- `f.NoSyncReload(ids)`: the free pages are `ids` (strictly increasing, from 2 on) but the pending ones; `ids` is only read. -/
def Interface.NoSyncReload.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState) (s : GoSlice) (ids : List Pgid) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ s ↦*{dq} ids ∗ ⌜idsOk ids⌝ }}
    (App (flCall fl go!"NoSyncReload") (Val #s))
  {{ RET #(); flOwn fl (F.reload ids) ∗ s ↦*{dq} ids }}

end spec

end Freelist
end EtcdGrove
end Perennial
