/-
The kv store's internal definitions: an item's and a key's resources, and the lock invariant of
`KV.mu` (the lab's `Kv/Defs.lean`; the client's share is `Store.lean`'s `storeOwn`, which the lab
had as `storeOwnK` pending its hub request H-kv-1).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Store
public import Dsverify.Proof.github_com.despreston.go_craq.store.kv.Base
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace kvp

/-- An item of the store: `(version, value, committed)`. -/
abbrev It := w64 × GoString × Bool

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [store.kv.Assumptions] [store.Assumptions]

/-- An item the store owns: a non-nil pointer, `itemPtr` and its `Committed` flag. -/
def itemOwn (p : Loc) (k : GoString) (it : It) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗ itemPtr p k it.1 it.2.1 ∗ structFieldRef store.Item go!"Committed" p ↦ it.2.2)

/-- The slice of key `k`: its items in order, with their pointers. -/
def keyOwn (k : GoString) (sl : GoSlice) (l : List (Loc × It)) : IProp GF :=
  iprop(sl ↦* l.map Prod.fst ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
    [∗list] e ∈ l, itemOwn e.1 k e.2)

/-- Key `k`'s entry `sl` of the items map, in contents `S`: a non-empty slice of the key's items. -/
def keyInv (S : StoreS) (k : GoString) (sl : GoSlice) : IProp GF :=
  iprop(∃ l : List (Loc × It), keyOwn k sl l ∗ ⌜l ≠ [] ∧ S.items k = l.map Prod.snd⌝)

/-- The lock invariant of `KV.mu`: the items map and the store's half of the contents. -/
def lockInv (mp : Loc) (γs : GName) : IProp GF :=
  iprop(∃ (m : GMap GoString GoSlice) (S : StoreS), mp ↦$ m ∗ ghostVar γs (1 : Qp).half S ∗
    ⌜∀ k, m !! k = none → S.items k = []⌝ ∗ [∗map] k ↦ sl ∈ m, keyInv S k sl)

/-- The store at `p` (persistent): its fields and its lock. -/
def isKV (p : Loc) (γs : GName) : IProp GF :=
  iprop(∃ mp : Loc, structFieldRef store.kv.KV go!"items" p ↦□ mp ∗
    sync.isMutex (structFieldRef store.kv.KV go!"mu" p) (lockInv mp γs) ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.store.kv)

instance isKV_persistent (p : Loc) (γs : GName) : Persistent (isKV (hG := hG) p γs) := by
  unfold isKV; infer_instance

end defs

end kvp

end github_com.despreston.go_craq

end Perennial
