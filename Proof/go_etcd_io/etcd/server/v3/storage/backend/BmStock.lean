/-
**`b.mu`'s read slots past the batch transaction's** (backend-snapshot B3, 2026-11-21;
`notes/backend-snapshot-plan.md`, "The reader slot of `b.mu`"): the constructor's `actualMaxReaders`
slots of `b.mu`, one kept by the batch transaction, the others (`bmStock`, `rdSlotsN` of them) one in
each reader's token (`rdTok`'s `bmSlot`). The owner of the stock (`etc/bounds-allow.txt`). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section stock
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- One copy and `rdSlotsN` copies. -/
theorem rep_one_slots (A : IProp GF) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), A) ⊢
      A ∗ [∗list] _x ∈ List.replicate rdSlotsN (), A := by
  rw [← rdSlotsN_add_one, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  iframe

/-- **`b.mu`'s read slots past the batch transaction's** (backend-snapshot B3), one for each
reader's token, as one opaque resource: irreducible, so that framing in `newBackend` (whose context
holds other lists of `actualMaxReaders` slots) never unifies it with them (a replicated list of about
`2 ^ 30` elements: 61 GB, 2026-11-21). -/
@[irreducible] def bmStock (b db : Loc) : IProp GF :=
  iprop([∗list] _x ∈ List.replicate rdSlotsN (),
    sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db))

theorem bmStock_unfold (b db : Loc) :
    bmStock (GF := GF) b db ⊣⊢ [∗list] _x ∈ List.replicate rdSlotsN (),
      sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) := by
  unfold bmStock; exact .rfl

/-- `b.mu`'s slots from its initialization: the batch transaction's and the stock. -/
theorem bm_slots_split (b db : Loc) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
      sync.ownRWMutex (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db)) ⊢
    sync.ownRWMutex (GF := GF) (bF go!"mu" b) (fun q => bF go!"db" b ↦{DFrac.own q} db) ∗
      bmStock b db := by
  refine (rep_one_slots _).trans ?_
  iintro ⟨H1, H⟩
  iframe H1
  iapply (bmStock_unfold b db).2
  iexact H

end stock

end backend
end EtcdGrove
end Perennial
