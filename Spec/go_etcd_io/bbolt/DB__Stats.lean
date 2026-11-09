/-
`db.Stats()` (`db.go`): a copy of the statistics under `statlock`'s read lock.

**Users.** `backend.defrag`'s size (`backend.go:606`: `db.Stats().FreePageN` right after
`Begin(false)`), and the backend's metrics. Snippet: `ReqBackendRead`.

**Proof sketch.** `statlock.RLock` on a reader slot: the caller's `threadTok`, or the slot pair a
read transaction's token bought (`statSlot`, the old D2); copy the struct; release.

**Changes.** Unchanged (`statSlot` over a read transaction's view).

**Margin.** The statistics' values are not described.
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.Stats()`: some statistics; the reader slot (`statSlot`) comes back. -/
def DB.Stats.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (ns : Bool) (o : Option (Loc × TxView)),
  {{ isBolt (GF := GF) db γ ns ∗ statSlot γ o }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Stats")) (Val #()))
  {{ (s : Stats), RET #s; statSlot γ o }}

end spec

end Bbolt
end EtcdGrove
end Perennial
