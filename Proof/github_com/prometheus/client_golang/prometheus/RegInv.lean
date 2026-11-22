/-
prometheus's default registry over client_golang v1.24.1's real `Registry` (route (b),
notes/prom-registry.md, "Step 2"): the vocabulary of `(*Registry).Register`'s spec and the registry's
invariant.

* **The rights** (`idTok γ k`, exclusive): the element `k` of a ghost map `γ` the program's proof
  allocates itself (each closed proof, inside its `Hwp`), for a key `k` (a descriptor ID or a collector
  ID) no built-in collector registered. The registry's invariant owns the element of every registered
  key that is not a built-in's, so a holder of `idTok γ k` knows `k` unregistered.
* **What a collector describes** (`describes c ps`, persistent): `c.Describe(ch)` sends the descriptor
  pointers `ps`, in order, on an SPSC channel, and returns. Register reads each `*Desc` it receives
  (`desc.id`, `desc.fqName`, `desc.dimHash`, `desc.err`); the points-to of the descriptors are
  given beside (`[∗list] p;d ∈ ps;ds, p ↦□ d`).
* **The registry** (`isRegistry γ r`, persistent): the three map fields (read-only after
  `NewRegistry`) and the `RWMutex` guard of `regInv`: the maps at a fraction, the elements of the
  registered non-built-in keys at that fraction, and the registered names' clause (every registered
  name is a built-in's, or its label-free descriptor's ID is registered).
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.github_com.prometheus.client_golang.prometheus.Seed
public import Proof.github_com.prometheus.client_golang.prometheus.SpscPeek
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostMap
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prometheus

open Iris Iris.BI Iris.ProofMode
open github_com.prometheus.client_golang.prometheus

/-! ## The built-ins (the trusted `init()`'s constants) -/

/-- The keys the built-in collectors registered (`init()`): their descriptor IDs and collector IDs. -/
def builtinKeys : List w64 := seed.descIDs ++ seed.collectorIDs

/-- The names the built-in collectors registered (`init()`). -/
def builtinNames : List GoString := seed.dims.map (·.1)

/-- **The run's registry ghost name** (Option 4, notes/prom-registry.md): the ghost map `γ` whose
elements are the registration rights (`idTok γ k`) and whose registered keys' elements the default
registry's invariant owns. Chosen by the program's proof (each closed proof allocates it inside its
run, `letI : PromRegGS GF := ⟨γ⟩`); prometheus's package fact is parameterized by it
(`IsPkgInitParam`, `PkgInit.lean`). -/
class PromRegGS (GF : BundledGFunctors) where
  γ : GName

/-! ## What a collector registers -/

section pure
variable [GooseExts]

/-- The XOR of a list of IDs, from 0, in order (`collectorID ^= desc.id`, `registry.go:318-321`). -/
def xorAll (ks : List w64) : w64 := ks.foldl (· ^^^ ·) 0

theorem xorAll_snoc (ks : List w64) (k : w64) : xorAll (ks ++ [k]) = xorAll ks ^^^ k := by
  unfold xorAll; rw [List.foldl_append]; rfl

/-- The keys `Register` adds for the descriptors `ds` (IDs pairwise distinct: `descsOk`): their IDs
and the collector ID, their XOR, when it is not one of them. -/
def descKeys (ds : List Desc) : List w64 :=
  if xorAll (ds.map (·.id')) ∈ ds.map (·.id') then ds.map (·.id')
  else ds.map (·.id') ++ [xorAll (ds.map (·.id'))]

/-- A collector of one descriptor has one key, its descriptor's ID (= its collector ID). Stated for
any descriptor, so no literal's ID is ever computed. -/
theorem descKeys_one (d : Desc) : descKeys [d] = [d.id'] := by
  have h : xorAll [d.id'] = d.id' := by
    unfold xorAll; simp only [List.foldl_cons, List.foldl_nil]; exact BitVec.zero_xor
  unfold descKeys
  simp only [List.map_cons, List.map_nil, h, List.mem_singleton, ↓reduceIte]

theorem descKeys_ids (ds : List Desc) (k : w64) (h : k ∈ ds.map (·.id')) : k ∈ descKeys ds := by
  unfold descKeys; split <;> simp_all

theorem descKeys_xor (ds : List Desc) : xorAll (ds.map (·.id')) ∈ descKeys ds := by
  unfold descKeys; split <;> simp_all

theorem descKeys_mem (ds : List Desc) (k : w64) (h : k ∈ descKeys ds) :
    k ∈ ds.map (·.id') ∨ k = xorAll (ds.map (·.id')) := by
  unfold descKeys at h; split at h <;> simp_all

/-- Descriptors `Register` accepts and registers without error from a registry that has none of their
keys: some (fewer than `2^32`: `len(newDescIDs)` is a Go `int`), valid (`err` nil), each label-free (its ID its name's `descId`), no built-in name, names
and IDs pairwise distinct. -/
def descsOk (ds : List Desc) : Prop :=
  ds ≠ [] ∧ ds.length < 2 ^ 32 ∧ (ds.map (·.fqName')).Nodup ∧ (ds.map (·.id')).Nodup ∧
  ∀ d ∈ ds, d.err' = (interface.nil : GoInterface) ∧ d.id' = descId d.fqName' ∧
    d.fqName' ∉ builtinNames

end pure

/-! ## Maps built by inserts (`insertList`, `Seed.lean`) -/

section insertList
variable {K V : Type} [DecidableEq K]

theorem insertList_cons (p : K × V) (ps : List (K × V)) (M : GMap K V) :
    insertList (p :: ps) M = insertList ps (<[p.1 := p.2]> M) := rfl

theorem insertList_snoc (ps : List (K × V)) (p : K × V) (M : GMap K V) :
    insertList (ps ++ [p]) M = <[p.1 := p.2]> (insertList ps M) := by
  unfold insertList; rw [List.foldl_append]; rfl

/-- A key no pair has keeps its value. -/
theorem insertList_lookup_notin (ps : List (K × V)) (M : GMap K V) (k : K)
    (h : k ∉ ps.map Prod.fst) : insertList ps M !! k = M !! k := by
  induction ps generalizing M with
  | nil => rfl
  | cons a ps ih =>
    rw [insertList_cons, ih _ (fun h' => h (List.mem_cons_of_mem _ h'))]
    have hne : a.1 ≠ k := fun e => h (e ▸ List.mem_cons_self ..)
    exact GMap.lookup_insert_ne _ _ hne

/-- A pair's key gets its value (keys pairwise distinct). -/
theorem insertList_lookup_mem (ps : List (K × V)) (M : GMap K V) (k : K) (v : V)
    (hnd : (ps.map Prod.fst).Nodup) (h : (k, v) ∈ ps) : insertList ps M !! k = some v := by
  induction ps generalizing M with
  | nil => cases h
  | cons a ps ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [insertList_cons]
    rcases List.mem_cons.mp h with rfl | h
    · rw [insertList_lookup_notin _ _ _ hnd.1]; exact GMap.lookup_insert _ _ _
    · exact ih _ hnd.2 h

/-- A key with a value after the inserts had it in a pair, or before. -/
theorem insertList_lookup_cases (ps : List (K × V)) (M : GMap K V) (k : K) (v : V)
    (h : insertList ps M !! k = some v) : (k, v) ∈ ps ∨ M !! k = some v := by
  induction ps generalizing M with
  | nil => exact Or.inr h
  | cons a ps ih =>
    rw [insertList_cons] at h
    rcases ih _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · by_cases e : a.1 = k
      · subst e
        rw [GMap.lookup_insert] at h
        cases h
        exact Or.inl (List.mem_cons_self ..)
      · rw [GMap.lookup_insert_ne _ _ e] at h; exact Or.inr h

/-- With `()` values: a key is present iff listed or present before. -/
theorem insertList_unit_lookup (ks : List K) (M : GMap K Unit) (k : K) :
    insertList (ks.map (fun x => (x, ()))) M !! k = if k ∈ ks then some () else M !! k := by
  split
  · rename_i h
    induction ks generalizing M with
    | nil => cases h
    | cons a ks ih =>
      rw [List.map_cons, insertList_cons]
      by_cases hk : k ∈ ks
      · exact ih _ hk
      · rw [insertList_lookup_notin _ _ _ (by simpa using hk)]
        rcases List.mem_cons.mp h with rfl | h
        · exact GMap.lookup_insert _ _ _
        · exact absurd h hk
  · rename_i h
    exact insertList_lookup_notin _ _ _ (by simpa using h)

end insertList

/-- A map built by inserts into the empty map has only the pairs' keys. -/
theorem insertList_empty_keys {K V : Type} [DecidableEq K] (ps : List (K × V)) (S : List K)
    (h : ∀ p ∈ ps, p.1 ∈ S) : ∀ k v, insertList ps ∅ !! k = some v → k ∈ S := by
  intro k v hk
  rcases insertList_lookup_cases ps ∅ k v hk with hm | hm
  · exact h _ hm
  · simp at hm

/-- The trusted `init()`'s maps hold only built-in keys and names (`isRegistry_init`'s premises). -/
theorem seed_C_builtin [GooseExts] : ∀ k v,
    insertList (seed.collectorIDs.map (fun id => (id, (interface.nil : GoInterface)))) ∅ !! k = some v →
      k ∈ builtinKeys :=
  insertList_empty_keys _ _ (by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨id, hid, rfl⟩ := hp
    exact List.mem_append_right _ hid)

theorem seed_D_builtin : ∀ k v,
    insertList (seed.descIDs.map (fun id => (id, ()))) ∅ !! k = some v → k ∈ builtinKeys :=
  insertList_empty_keys _ _ (by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨id, hid, rfl⟩ := hp
    exact List.mem_append_left _ hid)

theorem seed_N_builtin : ∀ n h,
    insertList (seed.dims.map (fun nd => nd)) ∅ !! n = some h → n ∈ builtinNames :=
  insertList_empty_keys _ _ (by
    intro p hp
    simp only [List.map_id'] at hp
    exact List.mem_map_of_mem hp)

/-- `f d` of the `k`-th element is not `f` of an earlier one (`f` injective on the list). -/
theorem nodup_take_notin {α β : Type} (f : α → β) (ds : List α) (k : Nat) (d : α)
    (h : (ds.map f).Nodup) (hd : ds[k]? = some d) : f d ∉ (ds.take k).map f := by
  intro hm
  rw [← List.take_append_drop k ds, List.map_append, List.nodup_append] at h
  have hd' : d ∈ ds.drop k := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by rw [List.getElem?_drop]; simpa using hd⟩
  exact h.2.2 _ hm _ (List.mem_map_of_mem hd') rfl

theorem take_succ_of_getElem? {α : Type} (ds : List α) (k : Nat) (d : α) (hd : ds[k]? = some d) :
    ds.take (k + 1) = ds.take k ++ [d] := by
  rw [List.take_add_one, hd]; rfl

/-- `#()` is the only value of `Unit` (the values of `struct{}`, `descIDs`' elements). -/
instance unit_intoValInj [GooseExts] [GoGlobalContext] : go.IntoValInj Unit := ⟨fun _ _ _ => rfl⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The rights -/

/-- **The right to the key `k`** (exclusive): `k` is no built-in's, and the element `k` of the run's
ghost map `γ`. -/
def idTok (γ : GName) (k : w64) : IProp GF :=
  iprop(⌜k ∉ builtinKeys⌝ ∗ ghostMapElem (K := w64) (V := Unit) γ k (DFrac.own 1) ())

/-- The rights to the keys `ks`. -/
def idToks (γ : GName) (ks : List w64) : IProp GF := iprop([∗list] k ∈ ks, idTok γ k)

theorem idToks_cons (γ : GName) (k : w64) (ks : List w64) :
    idToks (GF := GF) γ (k :: ks) ⊣⊢ idTok γ k ∗ idToks γ ks := by
  unfold idToks; exact BigSepL.bigSepL_cons

theorem idToks_app (γ : GName) (ks1 ks2 : List w64) :
    idToks (GF := GF) γ (ks1 ++ ks2) ⊣⊢ idToks γ ks1 ∗ idToks γ ks2 := by
  unfold idToks; exact BigSepL.bigSepL_append

theorem idToks_singleton (γ : GName) (k : w64) : idToks (GF := GF) γ [k] ⊣⊢ idTok γ k := by
  unfold idToks; exact BigSepL.bigSepL_singleton

/-- The rights to the IDs of the names `n :: ns` and to the keys `ks`: those of `n`, then the rest
(a registering package's initializer takes its names' rights one by one; the IDs are never computed). -/
theorem idToks_names_cons (γ : GName) (n : GoString) (ns : List GoString) (ks : List w64) :
    idToks (GF := GF) γ ((n :: ns).map descId ++ ks) ⊣⊢
      idToks γ [descId n] ∗ idToks γ (ns.map descId ++ ks) := by
  rw [List.map_cons, List.cons_append]
  constructor
  · iintro H
    icases (idToks_cons (GF := GF) γ _ _).1 $$ H with ⟨H1, H2⟩
    iframe H2
    iapply (idToks_singleton (GF := GF) γ _).2
    iexact H1
  · iintro ⟨H1, H2⟩
    icases (idToks_singleton (GF := GF) γ _).1 $$ H1 with H1
    iapply (idToks_cons (GF := GF) γ _ _).2
    iframe

/-- The rights left once every name's is taken: the other keys'. -/
theorem idToks_names_nil (γ : GName) (ks : List w64) :
    idToks (GF := GF) γ (([] : List GoString).map descId ++ ks) ⊣⊢ idToks γ ks :=
  ⟨.rfl, .rfl⟩

/-- Two rights to one key are one too many. -/
theorem idTok_excl (γ : GName) (k : w64) : idTok (GF := GF) γ k ∗ idTok γ k ⊢ False := by
  unfold idTok
  iintro ⟨⟨-, H1⟩, ⟨-, H2⟩⟩
  ihave %H := ghostMapElem_ne _ k k _ () () $$ H1 H2
  exact (H rfl).elim

end defs

/-! ## What a collector describes (SPSC channels: `HasLC.hasLC`) -/

section describes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **`c` describes the descriptors `ps`** (persistent): `c.Describe(ch)`, on any SPSC channel of
descriptor pointers (any protocol `P`, `R`) whose producer has sent `sent`, given `P` of each of `ps`
at its position, sends `ps` in order and returns. The call is the one `Register`'s goroutine makes
(the `chan<- *Desc` conversion of the channel is the identity on its value). -/
def describes (c : GoInterfaceOk) (ps : List Loc) : IProp GF :=
  iprop(□ ∀ (γ : SpscNames) (ch : Loc) (P : Int → Loc → IProp GF) (R : List Loc → IProp GF)
      (sent : List Loc),
    isSpsc γ ch P R -∗ ([∗list] i ↦ p ∈ ps, P ((sent.length : Int) + i) p) -∗
      spscProducer γ sent -∗
      WP (App (Val #(methods c.ty go!"Describe" c.v)) (Val #ch))
        {{ v, ⌜v = #()⌝ ∗ spscProducer γ (sent ++ ps) }})

instance describes_persistent (c : GoInterfaceOk) (ps : List Loc) :
    Persistent (describes (GF := GF) c ps) := by
  unfold describes; infer_instance

/-- **The collector `c` describes exactly one descriptor**, named `n`, without const labels (its ID
`descId n`), valid: what a metric or metric vector constructor returns (`New<Kind>`, `New<Kind>Vec`;
their variable labels enter only the descriptor's `dimHash`). Persistent. -/
def collectorName (c : GoInterfaceOk) (n : GoString) : IProp GF :=
  iprop(∃ (p : Loc) (d : Desc), p ↦□ d ∗
    ⌜d.fqName' = n ∧ d.id' = descId n ∧ d.err' = (interface.nil : GoInterface)⌝ ∗ describes c [p])

instance collectorName_persistent (c : GoInterfaceOk) (n : GoString) :
    Persistent (collectorName (GF := GF) c n) := by
  unfold collectorName; infer_instance

end describes

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The registry -/

/-- The registry's share `q` of the element of a registered key: none for a built-in's. -/
def regKeyTok (γ : GName) (q : Qp) (k : w64) : IProp GF :=
  if k ∈ builtinKeys then iprop(emp) else ghostMapElem (K := w64) (V := Unit) γ k (DFrac.own q) ()

/-- The registered keys: the descriptor IDs and the collector IDs. -/
def regKeys (C : GMap w64 GoInterface) (D : GMap w64 Unit) : GMap w64 Unit := D ∪ C.domSet

/-- The registry's share `q` of the elements of the keys `K`. -/
def regKeysTok (γ : GName) (q : Qp) (K : GMap w64 Unit) : IProp GF :=
  iprop([∗map] k ↦ _u ∈ K, regKeyTok γ q k)

/-- The registered names' clause: each a built-in's, or its label-free descriptor's ID registered. -/
def namesOk (D : GMap w64 Unit) (N : GMap GoString w64) : Prop :=
  ∀ n h, N !! n = some h → n ∈ builtinNames ∨ D !! descId n = some ()

/-- **The registry's lock predicate at fraction `q`** (`r.mtx`'s, a writer holds it at 1): the maps
`collectorsByID` (at `mC`), `descIDs` (`mD`), `dimHashesByName` (`mN`), the registered keys'
elements, the names' clause. -/
def regInv (γ : GName) (mC mD mN : Loc) (q : Qp) : IProp GF :=
  iprop(∃ (C : GMap w64 GoInterface) (D : GMap w64 Unit) (N : GMap GoString w64),
    mC ↦${DFrac.own q} C ∗ mD ↦${DFrac.own q} D ∗ mN ↦${DFrac.own q} N ∗
    regKeysTok γ q (regKeys C D) ∗ ⌜namesOk D N⌝)

theorem regKeyTok_fractional (γ : GName) (k : w64) (q1 q2 : Qp) :
    regKeyTok (GF := GF) γ (q1 + q2) k ⊣⊢ regKeyTok γ q1 k ∗ regKeyTok γ q2 k := by
  unfold regKeyTok
  split
  · exact emp_sep.symm
  · exact (ghostMapElem_fractional (GF := GF) k γ ()).fractional q1 q2

theorem regKeysTok_fractional (γ : GName) (K : GMap w64 Unit) (q1 q2 : Qp) :
    regKeysTok (GF := GF) γ (q1 + q2) K ⊣⊢ regKeysTok γ q1 K ∗ regKeysTok γ q2 K := by
  unfold regKeysTok
  rw [← BigSepM.bigSepM_sep_eq]
  constructor
  · exact BigSepM.bigSepM_mono (fun _ => (regKeyTok_fractional γ _ q1 q2).1)
  · exact BigSepM.bigSepM_mono (fun _ => (regKeyTok_fractional γ _ q1 q2).2)

instance regInv_fractional (γ : GName) (mC mD mN : Loc) :
    Fractional (regInv (GF := GF) γ mC mD mN) where
  fractional q1 q2 := by
    have hC := fun (C : GMap w64 GoInterface) => (ownMap_fractional (GF := GF) mC C).fractional q1 q2
    have hD := fun (D : GMap w64 Unit) => (ownMap_fractional (GF := GF) mD D).fractional q1 q2
    have hN := fun (N : GMap GoString w64) => (ownMap_fractional (GF := GF) mN N).fractional q1 q2
    unfold regInv
    refine ⟨?_, ?_⟩
    · iintro ⟨%C, %D, %N, HC, HD, HN, HK, %Hn⟩
      icases (hC C).1 $$ HC with ⟨HC1, HC2⟩
      icases (hD D).1 $$ HD with ⟨HD1, HD2⟩
      icases (hN N).1 $$ HN with ⟨HN1, HN2⟩
      icases (regKeysTok_fractional γ _ q1 q2).1 $$ HK with ⟨HK1, HK2⟩
      isplitl [HC1 HD1 HN1 HK1]
      · iexists C, D, N; iframe; ipureintro; exact Hn
      · iexists C, D, N; iframe; ipureintro; exact Hn
    · iintro ⟨⟨%C, %D, %N, HC, HD, HN, HK, %Hn⟩, ⟨%C2, %D2, %N2, HC2, HD2, HN2, HK2, -⟩⟩
      ihave %hc := ownMap_agree mC _ _ C C2 $$ [HC HC2]
      · iframe
      ihave %hd := ownMap_agree mD _ _ D D2 $$ [HD HD2]
      · iframe
      ihave %hn := ownMap_agree mN _ _ N N2 $$ [HN HN2]
      · iframe
      subst hc hd hn
      iexists C, D, N
      isplitl [HC HC2]
      · iapply (hC C).2; iframe
      isplitl [HD HD2]
      · iapply (hD D).2; iframe
      isplitl [HN HN2]
      · iapply (hN N).2; iframe
      isplitl [HK HK2]
      · iapply (regKeysTok_fractional γ _ q1 q2).2; iframe
      ipureintro; exact Hn

/-- **The registry `r`** (persistent): its map fields (read-only after `NewRegistry`) and the guard of
its lock, whose predicate is `regInv γ`. -/
def isRegistry (γ : GName) (r : Loc) : IProp GF :=
  iprop(∃ (mC mD mN : Loc),
    structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"collectorsByID" r ↦□ mC ∗
    structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"descIDs" r ↦□ mD ∗
    structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"dimHashesByName" r ↦□ mN ∗
    sync.isRWMutexGuard (structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"mtx" r) (regInv γ mC mD mN))

instance isRegistry_persistent (γ : GName) (r : Loc) : Persistent (isRegistry (GF := GF) γ r) := by
  unfold isRegistry; infer_instance

/-! ## Rights against the registry -/

/-- A held right is not a registered key. -/
theorem regKeysTok_absent (γ : GName) (K : GMap w64 Unit) (k : w64) :
    regKeysTok (GF := GF) γ 1 K ∗ idTok γ k ⊢
      ⌜K !! k = none⌝ ∗ regKeysTok γ 1 K ∗ idTok γ k := by
  iintro ⟨HK, Hk⟩
  cases h : K !! k with
  | none => iframe; ipureintro; rfl
  | some u =>
    iexfalso
    unfold regKeysTok
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (Φ := fun k' (_ : Unit) => regKeyTok (GF := GF) γ 1 k')
      (m := K) (i := k) (x := u) h).1 $$ HK with ⟨Hk', -⟩
    unfold idTok
    icases Hk with ⟨%hb, Hk⟩
    unfold regKeyTok
    rw [if_neg hb]
    ihave %H := ghostMapElem_ne _ k k _ () () $$ Hk Hk'
    exact (H rfl).elim

/-- Every held right is not a registered key. -/
theorem regKeysTok_absent_all (γ : GName) (K : GMap w64 Unit) (ks : List w64) :
    regKeysTok (GF := GF) γ 1 K ∗ idToks γ ks ⊢
      ⌜∀ k ∈ ks, K !! k = none⌝ ∗ regKeysTok γ 1 K ∗ idToks γ ks := by
  induction ks with
  | nil => iintro ⟨HK, Hk⟩; iframe; ipureintro; intro k hk; cases hk
  | cons a ks ih =>
    iintro ⟨HK, Hks⟩
    icases (idToks_cons (GF := GF) γ a ks).1 $$ Hks with ⟨Ha, Hks⟩
    icases regKeysTok_absent (GF := GF) γ K a $$ [HK Ha] with ⟨%h1, HK, Ha⟩
    · iframe
    icases ih $$ [HK Hks] with ⟨%h2, HK, Hks⟩
    · iframe
    iframe HK
    isplitr
    · ipureintro
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact h1
      · exact h2 k hk
    iapply (idToks_cons (GF := GF) γ a ks).2
    iframe

/-- The keys `ks` inserted, in order. -/
def insertKeys (ks : List w64) (K : GMap w64 Unit) : GMap w64 Unit :=
  ks.foldl (fun m k => <[k := ()]> m) K

theorem insertKeys_lookup (ks : List w64) (K : GMap w64 Unit) (k : w64) :
    insertKeys ks K !! k = if k ∈ ks then some () else K !! k := by
  induction ks generalizing K with
  | nil => rfl
  | cons a ks ih =>
    unfold insertKeys at *
    rw [List.foldl_cons, ih]
    by_cases e : a = k
    · subst e; simp
    · rw [GMap.lookup_insert_ne _ _ e]; simp [Ne.symm e]

/-- The held rights given to the registry. -/
theorem regKeysTok_insertKeys (γ : GName) (K : GMap w64 Unit) (ks : List w64) :
    regKeysTok (GF := GF) γ 1 K ∗ idToks γ ks ⊢ regKeysTok γ 1 (insertKeys ks K) := by
  induction ks generalizing K with
  | nil => iintro ⟨HK, -⟩; simp only [insertKeys, List.foldl_nil]; iexact HK
  | cons a ks ih =>
    iintro ⟨HK, Hks⟩
    icases (idToks_cons (GF := GF) γ a ks).1 $$ Hks with ⟨Ha, Hks⟩
    icases regKeysTok_absent (GF := GF) γ K a $$ [HK Ha] with ⟨%h1, HK, Ha⟩
    · iframe
    rw [show insertKeys (a :: ks) K = insertKeys ks (<[a := ()]> K) from rfl]
    iapply (ih (<[a := ()]> K))
    iframe Hks
    unfold regKeysTok
    iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (Φ := fun k' (_ : Unit) => regKeyTok (GF := GF) γ 1 k')
      (m := K) (i := a) (x := ()) h1).2
    iframe HK
    iunfold idTok at Ha
    icases Ha with ⟨%hb, Ha⟩
    unfold regKeyTok
    rw [if_neg hb]
    iexact Ha

/-- Built-in keys need no element. -/
theorem regKeysTok_builtin (γ : GName) (K : GMap w64 Unit)
    (hK : ∀ k u, K !! k = some u → k ∈ builtinKeys) :
    ⊢ regKeysTok (GF := GF) γ 1 K := by
  unfold regKeysTok
  refine BigSepM.bigSepM_intro (fun {k u} h => ?_)
  unfold regKeyTok
  rw [if_pos (hK k u h)]

/-- **A registry from its fields** (prometheus's initializer, after `defaultRegistry = NewRegistry()`
and the trusted `init()`'s seeding): the field points-to of the allocated `Registry` (its lock the
zero `RWMutex`) and its maps, holding only built-in keys and names, make `isRegistry γ r` for any
`γ` (the built-ins need no right). -/
theorem isRegistry_init [sync.Assumptions] (γ : GName) (r mC mD mN : Loc) (C : GMap w64 GoInterface)
    (D : GMap w64 Unit) (N : GMap GoString w64)
    (hC : ∀ k v, C !! k = some v → k ∈ builtinKeys) (hD : ∀ k u, D !! k = some u → k ∈ builtinKeys)
    (hN : ∀ n h, N !! n = some h → n ∈ builtinNames) :
    ⊢ structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"mtx" r ↦ (zero_val _root_.Perennial.sync.RWMutex) -∗
      structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"collectorsByID" r ↦ mC -∗
      structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"descIDs" r ↦ mD -∗
      structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"dimHashesByName" r ↦ mN -∗
      mC ↦$ C -∗ mD ↦$ D -∗ mN ↦$ N ={⊤}=∗ isRegistry (GF := GF) γ r := by
  iintro Hmtx HfC HfD HfN HC HD HN
  imod (update_into_persistently (P := structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"collectorsByID" r ↦ mC)) $$ HfC with #HfC
  imod (update_into_persistently (P := structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"descIDs" r ↦ mD)) $$ HfD with #HfD
  imod (update_into_persistently (P := structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"dimHashesByName" r ↦ mN)) $$ HfN with #HfN
  ihave HK : regKeysTok (GF := GF) γ 1 (regKeys C D) $$ []
  · iapply regKeysTok_builtin (GF := GF) γ (regKeys C D) (by
    intro k u h
    unfold regKeys at h
    rw [gmap_lookup_union] at h
    cases h1 : D !! k with
    | some u' => exact hD k u' h1
    | none =>
      rw [h1] at h
      simp only [Option.none_or] at h
      have := (GMap.lookup_fmap_Some (fun _ => ()) C k u).1 h
      obtain ⟨v, -, hv⟩ := this
      exact hC k v hv)
  imod (sync.init_RWMutex (regInv (GF := GF) γ mC mD mN) (E := ⊤)
      (structFieldRef github_com.prometheus.client_golang.prometheus.Registry go!"mtx" r)) $$ [HC HD HN HK] Hmtx with Hslots
  · inext
    unfold regInv
    iexists C, D, N
    iframe
    ipureintro
    intro n h hn
    exact Or.inl (hN n h hn)
  icases sync.ownRWMutex_slots_guard _ _ $$ Hslots with ⟨-, #Hg⟩
  imodintro
  unfold isRegistry
  iexists mC, mD, mN
  iframe #

end defs

section describes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A one-descriptor collector, as `Register`'s spec takes it**: `collectorName c n` of a name no
built-in has gives the descriptor `Register` reads, its points-to, `descsOk`, and its one key
`descId n` (the rights a registration of `c` needs: `idToks γ [descId n]`). -/
theorem collectorName_desc (c : GoInterfaceOk) (n : GoString) (hn : n ∉ builtinNames) :
    collectorName (GF := GF) c n ⊢ ∃ (p : Loc) (d : Desc), describes c [p] ∗
      ([∗list] p;d ∈ [p];[d], p ↦□ d) ∗ ⌜descsOk [d] ∧ descKeys [d] = [descId n]⌝ := by
  unfold collectorName
  iintro ⟨%p, %d, #Hp, %Hd, #Hdesc⟩
  obtain ⟨hname, hid, herr⟩ := Hd
  iexists p, d
  iframe Hdesc
  isplitl
  · iapply BigSepL2.bigSepL2_cons.2
    iframe Hp
    iapply BigSepL2.bigSepL2_nil.2
    iempintro
  ipureintro
  refine ⟨⟨List.cons_ne_nil _ _, by simp, by simp, by simp, ?_⟩, ?_⟩
  · intro d' hd'
    rcases List.mem_singleton.mp hd' with rfl
    exact ⟨herr, by rw [hid, hname], by rw [hname]; exact hn⟩
  · rw [descKeys_one, hid]

end describes

/-! ## The registry after a registration -/

section after
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

/-- The keys registered after `Register` inserts the IDs (`keysD`, the keys of `newDescIDs`) and the
collector ID: the keys before plus `descKeys ds`. -/
theorem regKeys_after (C : GMap w64 GoInterface) (D : GMap w64 Unit) (ds : List Desc)
    (keysD : List w64) (c : GoInterface) (hD : ∀ x, x ∈ keysD ↔ x ∈ ds.map (·.id')) :
    insertKeys (descKeys ds) (regKeys C D) =
      regKeys (<[xorAll (ds.map (·.id')) := c]> C) (insertList (keysD.map (fun x => (x, ()))) D) := by
  apply GMap.map_eq; intro x
  rw [insertKeys_lookup]
  unfold regKeys GMap.domSet
  simp only [GMap.lookup_union, GMap.lookup_fmap, insertList_unit_lookup]
  by_cases hx : x ∈ descKeys ds
  · rw [if_pos hx]
    rcases descKeys_mem ds x hx with h | h
    · rw [if_pos ((hD x).2 h)]; rfl
    · subst h; rw [GMap.lookup_insert]; split
      · rfl
      · cases D !! xorAll (ds.map (·.id')) <;> rfl
  · rw [if_neg hx]
    have h1 : x ∉ ds.map (·.id') := fun h => hx (descKeys_ids _ _ h)
    have h2 : xorAll (ds.map (·.id')) ≠ x := fun h => hx (h ▸ descKeys_xor ds)
    rw [if_neg (fun h => h1 ((hD x).1 h)), GMap.lookup_insert_ne _ _ h2]

/-- The names' clause after `Register` inserts the names (`keysN`, the keys of `newDimHashesByName`,
built from `ds`) and the IDs (`keysD`). -/
theorem namesOk_after (D : GMap w64 Unit) (N : GMap GoString w64) (ds : List Desc)
    (keysD : List w64) (keysN : List GoString) (f : GoString → w64)
    (hD : ∀ x, x ∈ keysD ↔ x ∈ ds.map (·.id'))
    (hN : ∀ n, n ∈ keysN →
      (insertList (ds.map (fun d => (d.fqName', d.dimHash'))) ∅ !! n).isSome)
    (hid : ∀ d ∈ ds, d.id' = descId d.fqName')
    (hok : namesOk D N) :
    namesOk (insertList (keysD.map (fun x => (x, ()))) D)
      (insertList (keysN.map (fun n => (n, f n))) N) := by
  intro n h hn
  rw [insertList_unit_lookup]
  rcases insertList_lookup_cases _ _ _ _ hn with hm | hm
  · right
    have hnk : n ∈ keysN := by
      obtain ⟨n', hn', he⟩ := List.mem_map.mp hm
      cases he; exact hn'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hN n hnk)
    rcases insertList_lookup_cases _ _ _ _ hv with hm' | hm'
    · obtain ⟨d, hd, he⟩ := List.mem_map.mp hm'
      cases he
      rw [if_pos ((hD _).2 (by rw [← hid d hd]; exact List.mem_map_of_mem hd))]
    · cases hm'
  · rcases hok n h hm with hb | hD'
    · exact Or.inl hb
    · right; split
      · rfl
      · exact hD'

end after

end prometheus
end EtcdGrove
end Perennial
