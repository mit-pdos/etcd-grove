/-
The ownership predicates of client-go's thread-safe store (`tools/cache/thread_safe_store.go`),
over its pure model (`StoreModel.lean`). Lean-first.

* `ownIxN l dq X`: one indexer's index, the map `l` from values to sets, each set owned.
* `Fn GF`: an index function's contract, a relation between an object and its values (functional,
  `fnFun`); `fnOk` says the Go function returns values the relation holds of. `objVals`/`valsOk`:
  an object's values under one/all indexers (none for `nil`); `itemsIv`: the items' recorded
  values (`StoreModel.lean`'s `IV`) meet them; `idxSel`: what an index query (`ByIndex`,
  `Index`) returns, the items whose recorded values meet a condition, with the relation's facts.
-/
module

public import Proof.k8s_io.client_go.tools.cache.StoreModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- One indexer's index at `l`: the map of values to the sets' locations, and each set's keys. -/
def ownIxN (l : Loc) (dq : DFrac) (X : IxN) : IProp GF :=
  iprop(l ↦${dq} (GMap.fmap Prod.fst X) ∗ [∗map] _v ↦ e ∈ X, e.1 ↦${dq} e.2)

/-- The indices at `ip`: the map of indexers' names to their indices, each index owned. -/
def ownIx (ip : Loc) (dq : DFrac) (ix : Ix) : IProp GF :=
  iprop(ip ↦${dq} (GMap.fmap Prod.fst ix) ∗ [∗map] _n ↦ e ∈ ix, ownIxN e.1 dq e.2)

open Iris.ProofMode in
/-- **Reading a set of the indices**: value `v`'s set of indexer `n`'s index: none (its location
`nil`, no keys), or its points-to, to give back. -/
theorem ownIx_set_acc (ip : Loc) (dq : DFrac) (ix : Ix) (n v : GoString) :
    ownIx (GF := GF) ip dq ix ⊢
      (⌜setLoc ix n v = null ∧ viewN (ixAt ix n) v = ∅⌝ ∗ ownIx ip dq ix) ∨
      (setLoc ix n v ↦${dq} viewN (ixAt ix n) v ∗
        (setLoc ix n v ↦${dq} viewN (ixAt ix n) v -∗ ownIx ip dq ix)) := by
  iintro Hix
  cases hn : ix !! n with
  | none =>
    have hs : setLoc ix n v = null := by unfold setLoc; rw [hn]; rfl
    have hv : viewN (ixAt ix n) v = ∅ := by unfold viewN ixAt; rw [hn]; rfl
    rw [hs, hv]
    ileft
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  | some e =>
    obtain ⟨l, X⟩ := e
    iunfold ownIx at Hix
    icases Hix with ⟨Hip, HIX⟩
    icases (BigSepM.bigSepM_lookup_acc hn) $$ HIX with ⟨HX, HIXc⟩
    iunfold ownIxN at HX
    icases HX with ⟨Hl, HXs⟩
    cases hv : X !! v with
    | none =>
      have hs : setLoc ix n v = null := by unfold setLoc; rw [hn]; simp [hv]
      have hv' : viewN (ixAt ix n) v = ∅ := by unfold viewN ixAt; rw [hn]; simp [hv]
      rw [hs, hv']
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iunfold ownIx
      iframe
      iapply HIXc
      iunfold ownIxN
      iframe
    | some e =>
      obtain ⟨s, S⟩ := e
      have hs : setLoc ix n v = s := by unfold setLoc; rw [hn]; simp [hv]
      have hv' : viewN (ixAt ix n) v = S := by unfold viewN ixAt; rw [hn]; simp [hv]
      rw [hs, hv']
      icases (BigSepM.bigSepM_lookup_acc hv) $$ HXs with ⟨Hs, HXsc⟩
      iright
      iframe Hs
      iintro Hs
      iunfold ownIx
      iframe
      iapply HIXc
      iunfold ownIxN
      iframe
      iapply HXsc $$ Hs

/-- An object the store may hold: `nil`, or one meeting the client's contract `OK`. -/
def okNil (OK : GoInterface → IProp GF) (o : GoInterface) : IProp GF :=
  iprop(⌜o = interface.nil⌝ ∨ □ OK o)

instance okNil_persistent (OK : GoInterface → IProp GF) (o : GoInterface) :
    Persistent (okNil OK o) := by
  unfold okNil; infer_instance

/-- **An index function's contract**, as a relation between an object and its values (persistent
facts of the heap, e.g. the object's fields' read-only points-to: an index function reads the
object, so its values are no pure function of the interface value). -/
abbrev Fn (GF : BundledGFunctors) : Type _ := GoInterface → List GoString → IProp GF

/-- The relation `F` is functional (the index function is deterministic on the objects it
indexes). -/
def fnFun (F : Fn GF) : IProp GF :=
  iprop(□ ∀ (o : GoInterface) (vs vs' : List GoString), □ F o vs -∗ □ F o vs' -∗ ⌜vs = vs'⌝)

instance fnFun_persistent (F : Fn GF) : Persistent (fnFun F) := by
  unfold fnFun; infer_instance

/-- **An index function's contract**: `f` is not `nil`, its relation `F` is functional, and on an
object meeting `OK` it returns no error and values `vs` with `F o vs` (in a slice the caller may
read). -/
def fnOk (OK : GoInterface → IProp GF) (f : GoFunc) (F : Fn GF) : IProp GF :=
  iprop(⌜f ≠ func.nil⌝ ∗ fnFun F ∗ ∀ o : GoInterface, {{ □ OK o }} (App (Val #f) (Val #o))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
        ⌜err = interface.nil⌝ ∗ ∃ (dq : DFrac) (vs : List GoString), sl ↦*{dq} vs ∗ □ F o vs }})

instance fnOk_persistent (OK : GoInterface → IProp GF) (f : GoFunc) (F : Fn GF) :
    Persistent (fnOk OK f F) := by
  unfold fnOk; infer_instance

/-- **The indexers' contracts**: the indexers' map `fv` has the indexers of `fns`, each function
meeting its contract. -/
def fnsOk (OK : GoInterface → IProp GF) (fv : GMap GoString GoFunc) (fns : GMap GoString (Fn GF)) :
    IProp GF :=
  iprop(⌜∀ n, n ∈ fns ↔ n ∈ fv⌝ ∗ [∗map] n ↦ f ∈ fv, ∃ F, ⌜fns !! n = some F⌝ ∗ fnOk OK f F)

instance fnsOk_persistent (OK : GoInterface → IProp GF) (fv : GMap GoString GoFunc)
    (fns : GMap GoString (Fn GF)) : Persistent (fnsOk OK fv fns) := by
  unfold fnsOk; infer_instance

/-- **An object's values under one indexer** (relation `F`): none for `nil` (never indexed),
otherwise values the relation holds of. -/
def objVals (F : Fn GF) (o : GoInterface) (vs : List GoString) : IProp GF :=
  iprop(⌜o = interface.nil ∧ vs = []⌝ ∨ (⌜o ≠ interface.nil⌝ ∗ □ F o vs))

instance objVals_persistent (F : Fn GF) (o : GoInterface) (vs : List GoString) :
    Persistent (objVals F o vs) := by
  unfold objVals; infer_instance

/-- **An object's index values** `vs` under the indexers `fns` (`objVals` for each). -/
def valsOk (fns : GMap GoString (Fn GF)) (o : GoInterface) (vs : Vals) : IProp GF :=
  iprop([∗map] n ↦ F ∈ fns, objVals F o (vsAt vs n))

instance valsOk_persistent (fns : GMap GoString (Fn GF)) (o : GoInterface) (vs : Vals) :
    Persistent (valsOk fns o vs) := by
  unfold valsOk; infer_instance

/-- **The items' recorded index values** `iv`: each item's values meet `valsOk`. -/
def itemsIv (fns : GMap GoString (Fn GF)) (it : Items) (iv : IV) : IProp GF :=
  iprop([∗map] k ↦ o ∈ it, valsOk fns o (ivOf iv k))

instance itemsIv_persistent (fns : GMap GoString (Fn GF)) (it : Items) (iv : IV) :
    Persistent (itemsIv fns it iv) := by
  unfold itemsIv; infer_instance

/-- **The items an index query selects** (`ByIndex`, `Index`): `ks` are items' keys, and an item is
among them exactly when its object is not `nil` and its values `vs` under the indexer (relation
`F`, holding of them) meet `S`. -/
def idxSel (F : Fn GF) (it : Items) (S : List GoString → Prop) (ks : List GoString) : IProp GF :=
  iprop(⌜∀ k, k ∈ ks → k ∈ it⌝ ∗
    [∗map] k ↦ o ∈ it, ∃ vs : List GoString,
      ⌜k ∈ ks ↔ (o ≠ interface.nil ∧ S vs)⌝ ∗ objVals F o vs)

instance idxSel_persistent (F : Fn GF) (it : Items) (S : List GoString → Prop)
    (ks : List GoString) : Persistent (idxSel F it S ks) := by
  unfold idxSel; infer_instance

open Iris.ProofMode in
/-- `nil`'s values: none. -/
theorem valsOk_nil (fns : GMap GoString (Fn GF)) (vs : Vals)
    (h : ∀ n, n ∈ fns → vsAt vs n = []) : ⊢ valsOk fns interface.nil vs := by
  unfold valsOk
  iapply (BigSepM.bigSepM_forall (Φ := fun n F => objVals F interface.nil (vsAt vs n))).2
  iintro %n %F %hn
  unfold objVals
  ileft; ipureintro
  refine ⟨rfl, h n ?_⟩
  rw [GMap.mem_iff, show fns !! n = some F from hn]; rfl

open Iris.ProofMode in
theorem objVals_nil (F : Fn GF) (vs : List GoString) :
    objVals F interface.nil vs ⊢ ⌜vs = []⌝ := by
  iintro H
  unfold objVals
  icases H with (%h | ⟨%h, -⟩)
  · ipureintro; exact h.2
  · exact absurd rfl h

open Iris.ProofMode in
/-- `valsOk`'s values of `nil`: none. -/
theorem valsOk_nil_pure (fns : GMap GoString (Fn GF)) (o : GoInterface) (vs : Vals) :
    valsOk fns o vs ⊢ ⌜o = interface.nil → ∀ n, n ∈ fns → vsAt vs n = []⌝ := by
  iintro #H
  by_cases ho : o = interface.nil
  · subst ho
    unfold valsOk
    ihave %h := (BigSepM.bigSepM_pure (φ := fun n (_ : Fn GF) => vsAt vs n = [])).1 $$ [H]
    · iapply (BigSepM.bigSepM_mono (fun {n F} _ => objVals_nil F (vsAt vs n))) $$ H
    ipureintro
    intro _ n hn
    rw [GMap.mem_iff] at hn
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.1 hn
    exact h n F hF
  · ipureintro; intro h; exact absurd h ho

open Iris.ProofMode in
/-- **The recorded values of a key's object** (absent: `nil`, none). -/
theorem itemsIv_lookup (fns : GMap GoString (Fn GF)) (it : Items) (iv : IV) (k : GoString)
    (hwf : ivWf fns it iv) :
    itemsIv fns it iv ⊢ valsOk fns (objAt it k) (ivOf iv k) := by
  iintro #H
  unfold itemsIv
  cases hk : it !! k with
  | some o =>
    have : objAt it k = o := by unfold objAt; rw [hk]; rfl
    rw [this]
    iapply (BigSepM.bigSepM_lookup hk) $$ H
  | none =>
    have : objAt it k = interface.nil := by unfold objAt; rw [hk]; rfl
    rw [this]
    iapply valsOk_nil
    intro n hn
    exact hwf k n (Or.inl this)

open Iris.ProofMode in
/-- The recorded values after storing `o` at `k` with values `vs`. -/
theorem itemsIv_insert (fns : GMap GoString (Fn GF)) (it : Items) (iv : IV) (k : GoString)
    (o : GoInterface) (vs : Vals) :
    itemsIv fns it iv ∗ valsOk fns o vs ⊢ itemsIv fns (<[k := o]> it) (<[k := vs]> iv) := by
  iintro ⟨#H, #Hv⟩
  unfold itemsIv
  iapply (BigSepM.bigSepM_forall (Φ := fun k' o' => valsOk fns o' (ivOf (<[k := vs]> iv) k'))).2
  iintro %k' %o' %hk'
  rw [ivOf_insert]
  change (<[k := o]> it) !! k' = some o' at hk'
  by_cases hkk : k' = k
  · subst hkk
    simp only [GMap.lookup_insert, Option.some.injEq] at hk'
    subst hk'
    simp only [↓reduceIte]
    iexact Hv
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)] at hk'
    simp only [hkk, ↓reduceIte]
    iapply (BigSepM.bigSepM_lookup hk') $$ H

open Iris.ProofMode in
/-- The recorded values after deleting `k` (whatever values it is given). -/
theorem itemsIv_delete (fns : GMap GoString (Fn GF)) (it : Items) (iv : IV) (k : GoString)
    (vs : Vals) :
    itemsIv fns it iv ⊢ itemsIv fns (GMap.delete k it) (<[k := vs]> iv) := by
  iintro #H
  unfold itemsIv
  iapply (BigSepM.bigSepM_forall (Φ := fun k' o' => valsOk fns o' (ivOf (<[k := vs]> iv) k'))).2
  iintro %k' %o' %hk'
  rw [ivOf_insert]
  change (GMap.delete k it) !! k' = some o' at hk'
  by_cases hkk : k' = k
  · subst hkk
    rw [GMap.lookup_delete] at hk'
    cases hk'
  · rw [GMap.lookup_delete_ne _ (Ne.symm hkk)] at hk'
    simp only [hkk, ↓reduceIte]
    iapply (BigSepM.bigSepM_lookup hk') $$ H

open Iris.ProofMode in
/-- **An index query's result**: the keys `ks` whose recorded values under indexer `n` (relation
`F`) meet `S` (which no key without values meets) are what `idxSel` describes. -/
theorem idxSel_of (fns : GMap GoString (Fn GF)) (it : Items) (iv : IV) (n : GoString) (F : Fn GF)
    (S : List GoString → Prop) (ks : List GoString) (hF : fns !! n = some F)
    (hwf : ivWf fns it iv) (hS : ¬ S []) (hks : ∀ k, k ∈ ks ↔ S (ivAt iv n k)) :
    itemsIv fns it iv ⊢ idxSel F it S ks := by
  iintro #H
  have hn : n ∈ fns := by rw [GMap.mem_iff, hF]; rfl
  unfold idxSel
  isplitr
  · ipureintro
    intro k hk
    have h1 := (hks k).1 hk
    rw [GMap.mem_iff]
    cases hk' : it !! k with
    | none =>
      have : objAt it k = interface.nil := by unfold objAt; rw [hk']; rfl
      rw [hwf k n (Or.inl this)] at h1
      exact absurd h1 hS
    | some _ => rfl
  iapply (BigSepM.bigSepM_forall (Φ := fun k o => iprop(∃ vs : List GoString,
      ⌜k ∈ ks ↔ (o ≠ interface.nil ∧ S vs)⌝ ∗ objVals F o vs))).2
  iintro %k %o %hk
  iexists ivAt iv n k
  unfold itemsIv
  ihave #Hv := (BigSepM.bigSepM_lookup hk) $$ H
  unfold valsOk
  ihave #Hvn := (BigSepM.bigSepM_lookup hF) $$ Hv
  isplitr
  · ipureintro
    rw [hks k]
    constructor
    · intro h
      refine ⟨fun ho => ?_, h⟩
      have : objAt it k = interface.nil := by
        unfold objAt; rw [show it !! k = some o from hk, ho]; rfl
      rw [hwf k n (Or.inl this)] at h
      exact hS h
    · exact fun h => h.2
  · unfold ivAt; iexact Hvn

/-- The indexers' map in two halves. -/
theorem fvMap_halves (l : Loc) (fv : GMap GoString GoFunc) (q : Qp) :
    (l ↦${DFrac.own q} fv : IProp GF) ⊣⊢ l ↦${DFrac.own q.half} fv ∗ l ↦${DFrac.own q.half} fv := by
  conv => lhs; rw [← Qp.half_add_half q]
  exact (ownMap_fractional (GF := GF) l fv).fractional _ _

end defs

end cache
end EtcdGrove
end Perennial
