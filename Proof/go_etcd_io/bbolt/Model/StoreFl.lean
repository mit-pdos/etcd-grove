/-
The synced freelist page in the page store (session S4, for `Tx.WriteTo`, S4a's blocker 2): the
page's extent, the slots the store keeps half of the page-cache bytes of while the page is the
committed state's and not freed (`flxS`), and the store's facts about it (`flxOK`): the page is
valid (`flPgOK`) for the committed state, and every registered reader's recorded page (its
committed state's, `RdInfo.fx`) is still there, with the same bytes, as that page's half or as
pending store slots the release spares (the MVCC rule of `mvccView`, for the page's slots).

Etcd runs bbolt with `NoFreelistSync`, so a committed state has a synced freelist page only when
`Open` read one (`init`'s, or a file written without the option); `Commit` frees it and never
writes another (`isBolt` records the option), so the page is the opened state's.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Store
public import Proof.go_etcd_io.bbolt.Model.FlPg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

section storefl
variable [GooseExts]

/-- The bytes of the extent starting at slot `f`, read from the slots' bytes `wb`. -/
def extentBytes (wb : Nat → List w8) (f : Nat) : List w8 :=
  (List.range' f (1 + pageOverflow (wb f))).flatMap wb

/-- The slots of the extent starting at slot `f` (its header's overflow, in the slots' bytes). -/
def flExt (bytes : Nat → List w8) (f : Nat) : List Nat :=
  List.range' f (1 + pageOverflow (bytes f))

/-- **The synced freelist page's extent while the store holds half of its page-cache bytes**: the
committed state's synced freelist page `f`, not freed (`f` no pending slot). -/
def flxS (C : CommitSt) (fl : FLPg) (bytes : Nat → List w8) : List Nat :=
  match C.flpg with
  | some f => if f ∈ pendSlots fl then [] else flExt bytes f
  | none => []

/-- **A registered reader's freelist page is kept**: the reader `r` recorded the page `f` with the
bytes `bs`; they are the store's bytes of the page's extent (whole pages), the page's allocating
transaction (if recorded) is at most the reader's, and the page is still the committed state's,
not freed (the store's half, `flxS`), or every slot of it is pending and the release spares it
(`mvccView`'s rule: allocated at most at the reader's txid, freed after it), in an entry of a
committed transaction or, if the live writer's, freeing the committed state's page. -/
def rdFlOK (σ : StoreSt) (r : RdInfo) : Prop :=
  ∀ f bs, r.fx = some (f, bs) → bs = extentBytes σ.bytes f ∧
    (∀ s ∈ flExt σ.bytes f, (σ.bytes s).length = 4096) ∧
    (∀ a, σ.fl.allocs !! W64 (f : Int) = some a → a.toNat ≤ r.v.txid) ∧
    ((σ.C.flpg = some f ∧ f ∉ pendSlots σ.fl) ∨
     ∀ s ∈ flExt σ.bytes f, s ∈ pendSlots σ.fl ∧ W64 (s : Int) ∉ σ.fl.free ∧
       ∀ t pd i, σ.fl.pending !! t = some pd → pd.ids[i]? = some (W64 (s : Int)) →
         (pd.alloctx.getD i 0).toNat ≤ r.v.txid ∧ r.v.txid < t.toNat ∧
         (t.toNat ≤ σ.C.txid ∨ σ.C.flpg = some f))

/-- **The store's facts about the synced freelist page**: the committed state's page `f` is valid
for it (`flPgOK`), its slots' bytes are pages, never free, freed whole or not at all, and only by
the live writer before its publish, each pending slot's (and the page's) allocating transaction
committed; the registered readers' pages are kept (`rdFlOK`). -/
def flxOK (σ : StoreSt) : Prop :=
  (∀ f, σ.C.flpg = some f → flPgOK σ.C f (extentBytes σ.bytes f) ∧
    (∀ s ∈ flExt σ.bytes f, (σ.bytes s).length = 4096 ∧ W64 (s : Int) ∉ σ.fl.free ∧
      (s ∈ pendSlots σ.fl ↔ f ∈ pendSlots σ.fl) ∧
      (f ∈ pendSlots σ.fl → σ.pub = false ∧ pendingOnlyFromWriter σ.fl σ.wtx s) ∧
      ∀ t pd i, σ.fl.pending !! t = some pd → pd.ids[i]? = some (W64 (s : Int)) →
        (pd.alloctx.getD i 0).toNat ≤ σ.C.txid) ∧
    ∀ a, σ.fl.allocs !! W64 (f : Int) = some a → a.toNat ≤ σ.C.txid) ∧
  ∀ k r, σ.R !! k = some r → rdFlOK σ r

/-- **The page a reader registering now records**: the committed state's synced freelist page,
with the store's bytes of its extent. -/
def fxOf (σ : StoreSt) : Option (Nat × List w8) :=
  match σ.C.flpg with
  | some f => some (f, extentBytes σ.bytes f)
  | none => none

/-- **What a reader knows of its recorded page** `fx` (for `Tx.WriteTo`'s image): `C`'s synced
freelist page, if any, with bytes valid for `C` (`flPgOK`), in whole pages. -/
def fxOK (C : CommitSt) (fx : Option (Nat × List w8)) : Prop :=
  match C.flpg with
  | none => fx = none
  | some f => ∃ bs, fx = some (f, bs) ∧ flPgOK C f bs ∧
      bs.length = 4096 * (1 + pageOverflow bs)

end storefl

end bbolt
end EtcdGrove
end Perennial
