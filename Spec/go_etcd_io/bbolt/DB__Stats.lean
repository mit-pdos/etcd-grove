/-
`db.Stats()` (`db.go`): a copy of the statistics under `statlock`'s read lock.

**Users.** `backend.defrag`'s size (`backend.go:606`: `db.Stats().FreePageN` right after
`Begin(false)`), `backend.begin(true)` right after `Begin(true)` (`backend.go:1086-1098`, every
batch commit: holding only the write transaction), and the backend's metrics. Snippets:
`ReqBackendRead`, `ReqBackendBatch`.

**Proof sketch.** `statlock.RLock` on a reader slot: the caller's `threadTok`, or the slot pair a
read transaction's token bought (`statSlot`, the old D2), or, for a write transaction, the spare
`statlock` slot `isBolt` keeps for the writer (it holds `rwlock`: no other writer can use it);
copy the struct; release.

**Changes.** Verify-round (A11-completeness F4): `statSlot (some (tx, T))` accepts a write
transaction too (`statSlot_wtx`); was a read transaction's only, leaving the backend's
`begin(true)` with no slot to pay. Re-review (N6): a paying transaction is one of this `*DB`
(`txDB tx db`): a transaction of another `*DB` of the same file holds another `statlock`'s slot.

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
  {{ isBolt (GF := GF) db γ ns ∗ statSlot γ o ∗
      (match o with | some (tx, _) => txDB tx db | none => iprop(emp)) }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Stats")) (Val #()))
  {{ (s : Stats), RET #s; statSlot γ o }}

end spec

end Bbolt
end EtcdGrove
end Perennial
