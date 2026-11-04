/-
The writer side after `ReleasePendingPages` (U5 of `notes/bbolt-proof-plan.md`, `beginRWTx`): the
released slots (`store_release`'s `S`, no longer store slots) join the writer's `W` slots, with
their cells and page-cache bytes.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section release
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The writer side with the freelist `fl'` and the slots `S` (bytes `bs`) joined to its `W`
slots. -/
def WDb.released (w : WDb) (fl' : FLPg) (S : List Nat) (bs : Nat → List w8) : WDb :=
  { w with fl := fl', W := w.W ++ S, wb := fun s => if s ∈ S then bs s else w.wb s }

/-- **The writer side after `ReleasePendingPages`** (`beginRWTx`): from the idle store `σ`
(`storeOK`, no writer), the slots `S` released (`store_release`'s), whose bytes are whole pages
(`hbs`: not in `store_release`'s post, U5c's finding), the writer side's facts and its `W` slots'
cells and bytes extend to the released freelist. Open (U5c): the pure part is `wdbOK` clause by
clause (the released ids were committed-pending: below the mark, no tree slots, in the synced
freelist page's ids; the freelist page's slots are in no pending entry, so its bytes are kept),
the resources are `bytes_cellsR` and `osSlot` per slot of `S`. -/
theorem wdb_release (p : GoString) (w : WDb) (σ : StoreSt) (ro : List w64) (S : List Nat)
    (bs : Nat → List w8)
    (hσ : σ.C = w.C ∧ σ.fl = w.fl ∧ σ.ms = w.ms ∧ σ.wst = wIdle ∧ storeOK σ) (hok : wdbOK w)
    (hms : w.ms ≠ none)
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C (w.fl.releasePending ro))
    (hbs : ∀ s ∈ S, (bs s).length = 4096) :
    wCells (GF := GF) w.ms w.W ∗ wBytes p w.W w.wb w.m.size ∗ slotsOwn w.ms p S bs ⊢
      ⌜wdbOK (w.released (w.fl.releasePending ro) S bs)⌝ ∗
      wCells w.ms (w.released (w.fl.releasePending ro) S bs).W ∗
      wBytes p (w.released (w.fl.releasePending ro) S bs).W
        (w.released (w.fl.releasePending ro) S bs).wb w.m.size := by
  sorry

end release

end bbolt
end EtcdGrove
end Perennial
