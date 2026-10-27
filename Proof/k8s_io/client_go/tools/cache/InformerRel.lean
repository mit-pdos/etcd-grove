/-
**The informer's Go state and its abstract state** (phase 4 of `notes/k8s-daemonset-plan.md`, fourth
round): how the store's items (`cache.St`, Go objects by their key strings) and the FIFO's deltas
(`cache.FD`) are the contract's (`informer.View`, `informer.Delta`: the model's objects by key),
given a registry `R` of the Go objects' values (each Go object the informer handles is a read-only
copy of one of the model's objects, registered once). Lean-first.

* `keyStr`: the store's key of an object key (client-go's `MetaNamespaceKeyFunc`: `ns/name`, or
  `name` without a namespace), injective on keys without `/` (`keyGood`; Kubernetes' names and
  namespaces are DNS labels or subdomains, the model's are the program's: a premise).
* `storeRel R σs v`: the store's version is the view's (`""` before any) and its items are the
  view's, by key string.
* `fdRel R d a`: a queued Go delta is an abstract one.
* `storeRel_step`: one delta's store step (`storeStepFD`) is the view's `apply`; `storeRel_batch`:
  a batch's (`batchStore`) is `applyAll`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerContract
public import Proof.k8s_io.client_go.tools.cache.BatchDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open apimodel

section model
variable [FfiSyntax] [GoGlobalContext]

/-- The slash, as a byte. -/
def slashB : w8 := 47

/-- **The store's key string** of an object key (`MetaNamespaceKeyFunc`). -/
def keyStr (k : Key) : GoString :=
  if k.Namespace' = [] then k.Name' else k.Namespace' ++ slashB :: k.Name'

/-- A key whose namespace and name have no slash. -/
def keyGood (k : Key) : Prop := slashB ∉ k.Namespace' ∧ slashB ∉ k.Name'

theorem append_slash_inj : ∀ (a b c d : GoString), slashB ∉ a → slashB ∉ c →
    a ++ slashB :: b = c ++ slashB :: d → a = c ∧ b = d
  | [], b, [], d, _, _, h => by simpa using h
  | [], b, x :: c, d, _, hc, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hc
  | x :: a, b, [], d, ha, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) ha
  | x :: a, b, y :: c, d, ha, hc, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := append_slash_inj a b c d (fun h' => ha (List.mem_cons_of_mem _ h'))
        (fun h' => hc (List.mem_cons_of_mem _ h')) h
      exact ⟨by rw [this.1], this.2⟩

/-- **`keyStr` is injective on good keys.** -/
theorem keyStr_inj (k1 k2 : Key) (h1 : keyGood k1) (h2 : keyGood k2) (h : keyStr k1 = keyStr k2) :
    k1 = k2 := by
  obtain ⟨n1, m1⟩ := k1
  obtain ⟨n2, m2⟩ := k2
  unfold keyStr at h
  simp only at h h1 h2
  by_cases e1 : n1 = [] <;> by_cases e2 : n2 = []
  · simp only [e1, e2, ↓reduceIte] at h; subst e1; subst e2; subst h; rfl
  · simp only [e1, e2, ↓reduceIte] at h
    exact absurd (h ▸ List.mem_append_right n2 List.mem_cons_self) h1.2
  · simp only [e1, e2, ↓reduceIte] at h
    exact absurd (h ▸ List.mem_append_right n1 List.mem_cons_self) h2.2
  · simp only [e1, e2, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := append_slash_inj n1 m1 n2 m2 h1.1 h2.1 h
    rfl

/-- The FIFO's delta type of a change (`ADDED` → `Added`, `MODIFIED` → `Updated`, `DELETED` →
`Deleted`: the reflector's `Add`/`Update`/`Delete`). -/
def fdTypeOf : EvTy → GoString
  | .added => go!"Added"
  | .modified => go!"Updated"
  | .deleted => go!"Deleted"

/-- **The registry**: each Go object the informer handles, its model object. -/
abbrev Reg : Type := GMap GoInterface Obj

/-- A resource version string of a version `v` (`none`: `""`). -/
def rvRel (s : GoString) : Option Nat → Prop
  | none => s = []
  | some v => ∃ w : w64, v = w.toNat ∧ s = rvStr w

/-- **The store's items are the view's**, by key string: each the registered Go object of the
view's object at that key; the view's keys good. -/
def itemsRel (R : Reg) (its : cache.Items) (M : GMap Key Obj) : Prop :=
  (∀ key, key ∈ M → keyGood key) ∧ (∀ key o, M !! key = some o → o.key = key) ∧
  ∀ k, (∃ x o, its !! k = some x ∧ R !! x = some o ∧ keyStr o.key = k ∧ M !! o.key = some o) ∨
       (its !! k = none ∧ ∀ key, keyStr key = k → M !! key = none)

/-- **The store is the view**: its version, and its items. -/
def storeRel (R : Reg) (σs : cache.St) (v : View) : Prop :=
  rvRel σs.rv v.rv ∧ itemsRel R σs.items v.items

/-- **A list's Go objects are the map `M`'s objects**: each registered with an object of `M` at its
key, each of `M`'s objects one of them. -/
def listRel (R : Reg) (xs : List GoInterface) (M : GMap Key Obj) : Prop :=
  (∀ x ∈ xs, ∃ o, R !! x = some o ∧ M !! o.key = some o) ∧
  (∀ key o, M !! key = some o → ∃ x ∈ xs, R !! x = some o)

/-- **A queued Go delta is an abstract one.** -/
def fdRel (R : Reg) : cache.FD → Delta → Prop
  | .obj t x, .change c => t = fdTypeOf c.typ ∧ R !! x = some c.obj ∧ x ≠ interface.nil
  | .replaced xs rvs, .replaced M v => rvRel rvs (some v) ∧ listRel R xs M
  | .bookmark rvs, .bookmark v => rvRel rvs (some v)
  | _, _ => False

theorem lookup_none_of_good (M : GMap Key Obj) (hg : ∀ key, key ∈ M → keyGood key) (key k0 : Key)
    (hk0 : keyGood k0) (hne : key ≠ k0) (heq : keyStr key = keyStr k0) : M !! key = none := by
  cases hl : M !! key with
  | none => rfl
  | some o =>
    have hm : key ∈ M := by rw [GMap.mem_iff, hl]; rfl
    exact absurd (keyStr_inj _ _ (hg key hm) hk0 heq) hne

/-- **A put**: the Go object `x` of `o` stored at `o`'s key string. -/
theorem itemsRel_put (R : Reg) (its : cache.Items) (M : GMap Key Obj) (x : GoInterface) (o : Obj)
    (h : itemsRel R its M) (hx : R !! x = some o) (hgood : keyGood o.key) :
    itemsRel R (<[keyStr o.key := x]> its) (<[o.key := o]> M) := by
  obtain ⟨hg, hkd, hit⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro key hk
    rw [GMap.mem_iff, GMap.lookup_insert_eq_iff] at hk
    by_cases he : o.key = key
    · subst he; exact hgood
    · simp only [he, ↓reduceIte] at hk; exact hg key hk
  · intro key o' hk
    rw [GMap.lookup_insert_eq_iff] at hk
    by_cases he : o.key = key
    · simp only [he, ↓reduceIte, Option.some.injEq] at hk; subst hk; exact he
    · simp only [he, ↓reduceIte] at hk; exact hkd key o' hk
  · intro k
    by_cases hk : keyStr o.key = k
    · subst hk
      left
      exact ⟨x, o, by simp, hx, rfl, by simp⟩
    · rcases hit k with ⟨x', o', hx', hro, hko, hvo⟩ | ⟨hn, hnone⟩
      · left
        refine ⟨x', o', by simp [hk, hx'], hro, hko, ?_⟩
        have : o.key ≠ o'.key := fun he => hk (by rw [he, hko])
        simp [this, hvo]
      · right
        refine ⟨by simp [hk, hn], ?_⟩
        intro key hkey
        have : o.key ≠ key := fun he => hk (by rw [he, hkey])
        simp [this, hnone key hkey]

/-- **A delete**: the key string of `key0` removed. -/
theorem itemsRel_delete (R : Reg) (its : cache.Items) (M : GMap Key Obj) (key0 : Key)
    (h : itemsRel R its M) (hgood : keyGood key0) :
    itemsRel R (GMap.delete (keyStr key0) its) (GMap.delete key0 M) := by
  obtain ⟨hg, hkd, hit⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro key hk
    rw [GMap.mem_iff, GMap.lookup_delete_iff] at hk
    by_cases he : key0 = key
    · simp [he] at hk
    · simp only [he, ↓reduceIte] at hk; exact hg key hk
  · intro key o' hk
    rw [GMap.lookup_delete_iff] at hk
    by_cases he : key0 = key
    · simp [he] at hk
    · simp only [he, ↓reduceIte] at hk; exact hkd key o' hk
  · intro k
    by_cases hk : keyStr key0 = k
    · subst hk
      right
      refine ⟨by simp, ?_⟩
      intro key hkey
      by_cases hkk : key0 = key
      · simp [hkk]
      · rw [GMap.lookup_delete_iff]
        simp only [hkk, ↓reduceIte]
        exact lookup_none_of_good M hg key key0 hgood (Ne.symm hkk) hkey
    · rcases hit k with ⟨x', o', hx', hro, hko, hvo⟩ | ⟨hn, hnone⟩
      · left
        refine ⟨x', o', by simp [hk, hx'], hro, hko, ?_⟩
        have : key0 ≠ o'.key := fun he => hk (by rw [he, hko])
        simp [this, hvo]
      · right
        refine ⟨by simp [hk, hn], ?_⟩
        intro key hkey
        have : key0 ≠ key := fun he => hk (by rw [he, hkey])
        simp [this, hnone key hkey]

/-- **One change's store step is the view's.** -/
theorem storeRel_change (R : Reg) (KF : GoInterface → GoString)
    (rvOf : GoInterface → Option GoString) (σs : cache.St) (v : View) (c : Change) (x : GoInterface)
    (hR : storeRel R σs v) (hx : R !! x = some c.obj) (hkf : KF x = keyStr c.obj.key)
    (hgood : keyGood c.obj.key) (hrv : rvOf x = some (rvStr c.rv)) (hnil : x ≠ interface.nil) :
    storeRel R (cache.storeStepFD KF rvOf σs (.obj (fdTypeOf c.typ) x)) (v.apply (.change c)) := by
  obtain ⟨_, hit⟩ := hR
  unfold cache.storeStepFD View.apply applyChange
  cases ht : c.typ with
  | deleted =>
    simp only [fdTypeOf, ↓reduceIte, cache.St.delete, cache.rvOfObj, hnil, hrv, Option.getD_some,
      hkf, ht]
    exact ⟨⟨c.rv, rfl, rfl⟩, itemsRel_delete R _ _ _ hit hgood⟩
  | added =>
    simp only [fdTypeOf, cache.St.update, hrv, Option.getD_some, hkf, ht]
    rw [ite_eq_right (by decide)]
    exact ⟨⟨c.rv, rfl, rfl⟩, itemsRel_put R _ _ x c.obj hit hx hgood⟩
  | modified =>
    simp only [fdTypeOf, cache.St.update, hrv, Option.getD_some, hkf, ht]
    rw [ite_eq_right (by decide)]
    exact ⟨⟨c.rv, rfl, rfl⟩, itemsRel_put R _ _ x c.obj hit hx hgood⟩

/-- **A queued object delta of a watch change, with what the store needs of it**: its Go object
registered with the change's object, its key string the key function's, its key good, its version
the accessor's, not `nil`. -/
def objOk (R : Reg) (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString)
    (fd : cache.FD) (a : Delta) : Prop :=
  ∃ x c, fd = .obj (fdTypeOf c.typ) x ∧ a = .change c ∧ R !! x = some c.obj ∧
    KF x = keyStr c.obj.key ∧ keyGood c.obj.key ∧ rvOf x = some (rvStr c.rv) ∧ x ≠ interface.nil

theorem itemsRel_fdItems (R : Reg) (KF : GoInterface → GoString)
    (rvOf : GoInterface → Option GoString) (its : cache.Items) (v : View) (fd : cache.FD)
    (a : Delta) (h : itemsRel R its v.items) (ho : objOk R KF rvOf fd a) :
    itemsRel R (cache.fdItems KF its fd) (v.apply a).items := by
  obtain ⟨x, c, rfl, rfl, hx, hkf, hgood, -, -⟩ := ho
  unfold cache.fdItems View.apply applyChange
  simp only [hkf]
  cases ht : c.typ with
  | deleted => simp only [fdTypeOf, ↓reduceIte]; exact itemsRel_delete R _ _ _ h hgood
  | added =>
    split
    · exact absurd ‹_› (by decide)
    · exact itemsRel_put R _ _ x c.obj h hx hgood
  | modified =>
    split
    · exact absurd ‹_› (by decide)
    · exact itemsRel_put R _ _ x c.obj h hx hgood

theorem itemsRel_fold (R : Reg) (KF : GoInterface → GoString)
    (rvOf : GoInterface → Option GoString) :
    ∀ (ds : List cache.FD) (abs : List Delta) (its : cache.Items) (v : View),
      List.Forall₂ (objOk R KF rvOf) ds abs → itemsRel R its v.items →
      itemsRel R (ds.foldl (cache.fdItems KF) its) (v.applyAll abs).items
  | [], [], _, _, _, h => h
  | _ :: _, [], _, _, h, _ => by cases h
  | [], _ :: _, _, _, h, _ => by cases h
  | d :: ds, a :: abs, its, v, h, hi => by
    cases h with
    | cons hda hrest =>
      exact itemsRel_fold R KF rvOf ds abs _ (v.apply a) hrest (itemsRel_fdItems R KF rvOf its v d a hi hda)

theorem applyAll_rv_last (R : Reg) (KF : GoInterface → GoString)
    (rvOf : GoInterface → Option GoString) :
    (dflt : GoString) → ∀ (ds : List cache.FD) (abs : List Delta) (v : View) (d : cache.FD),
      List.Forall₂ (objOk R KF rvOf) ds abs → ds.getLast? = some d →
      rvRel ((rvOf d.obj?).getD dflt) (v.applyAll abs).rv
  | _, [], _, _, _, _, h => by simp at h
  | _, [d], [a], v, d', hf, hl => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    cases hf with
    | cons hda _ =>
      obtain ⟨x, c, rfl, rfl, -, -, -, hrv, -⟩ := hda
      simp only [cache.FD.obj?, hrv, Option.getD_some, View.applyAll, List.foldl_cons,
        List.foldl_nil, View.apply]
      exact ⟨c.rv, rfl, rfl⟩
  | dflt, d :: d2 :: ds, a :: abs, v, d', hf, hl => by
    cases hf with
    | cons hda hrest =>
      rw [List.getLast?_cons_cons] at hl
      exact applyAll_rv_last R KF rvOf dflt (d2 :: ds) abs (v.apply a) d' hrest hl
  | _, [_], [], _, _, hf, _ => by cases hf
  | _, [_], _ :: _ :: _, _, _, hf, _ => by cases hf with | cons _ h => cases h
  | _, _ :: _ :: _, [], _, _, hf, _ => by cases hf

/-- **A batch's store step is the view's `applyAll`.** -/
theorem storeRel_batch (R : Reg) (KF : GoInterface → GoString)
    (rvOf : GoInterface → Option GoString) (σs : cache.St) (v : View) (ds : List cache.FD)
    (abs : List Delta) (hR : storeRel R σs v) (hf : List.Forall₂ (objOk R KF rvOf) ds abs) :
    storeRel R (cache.batchStore KF rvOf σs ds) (v.applyAll abs) := by
  unfold cache.batchStore
  cases hl : ds.getLast? with
  | none =>
    have : ds = [] := List.getLast?_eq_none_iff.1 hl
    subst this
    cases hf
    exact hR
  | some d =>
    exact ⟨applyAll_rv_last R KF rvOf σs.rv ds abs v d hf hl,
      itemsRel_fold R KF rvOf ds abs σs.items v hf hR.2⟩

theorem keyedItems_lookup (KF : GoInterface → GoString) :
    ∀ (xs : List GoInterface) (m : cache.Items) (k : GoString) (x : GoInterface),
      (xs.foldl (fun m x => <[KF x := x]> m) m) !! k = some x →
        (x ∈ xs ∧ KF x = k) ∨ (m !! k = some x ∧ ∀ y ∈ xs, KF y ≠ k)
  | [], m, k, x, h => Or.inr ⟨h, by simp⟩
  | y :: xs, m, k, x, h => by
    simp only [List.foldl_cons] at h
    rcases keyedItems_lookup KF xs _ k x h with ⟨hx, hk⟩ | ⟨hm, hn⟩
    · exact Or.inl ⟨List.mem_cons_of_mem _ hx, hk⟩
    · rw [GMap.lookup_insert_eq_iff] at hm
      by_cases he : KF y = k
      · simp only [he, ↓reduceIte, Option.some.injEq] at hm
        subst hm
        exact Or.inl ⟨List.mem_cons_self, he⟩
      · simp only [he, ↓reduceIte] at hm
        refine Or.inr ⟨hm, ?_⟩
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact he
        · exact hn z hz

theorem keyedItems_none (KF : GoInterface → GoString) :
    ∀ (xs : List GoInterface) (m : cache.Items) (k : GoString),
      (xs.foldl (fun m x => <[KF x := x]> m) m) !! k = none → m !! k = none ∧ ∀ y ∈ xs, KF y ≠ k
  | [], m, k, h => ⟨h, by simp⟩
  | y :: xs, m, k, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨hm, hn⟩ := keyedItems_none KF xs _ k h
    rw [GMap.lookup_insert_eq_iff] at hm
    by_cases he : KF y = k
    · simp [he] at hm
    · simp only [he, ↓reduceIte] at hm
      refine ⟨hm, ?_⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact he
      · exact hn z hz

/-- **A relist's items**: the listed Go objects by key string are the list's map. -/
theorem itemsRel_keyed (R : Reg) (KF : GoInterface → GoString) (xs : List GoInterface)
    (M : GMap Key Obj) (hl : listRel R xs M)
    (hk : ∀ x ∈ xs, ∀ o, R !! x = some o → KF x = keyStr o.key)
    (hg : ∀ key, key ∈ M → keyGood key) (hkd : ∀ key o, M !! key = some o → o.key = key) :
    itemsRel R (cache.keyedItems KF xs) M := by
  refine ⟨hg, hkd, ?_⟩
  intro k
  cases hx : cache.keyedItems KF xs !! k with
  | some x =>
    left
    rcases keyedItems_lookup KF xs ∅ k x hx with ⟨hmem, hkx⟩ | ⟨hm, _⟩
    · obtain ⟨o, hro, hmo⟩ := hl.1 x hmem
      exact ⟨x, o, rfl, hro, by rw [← hk x hmem o hro, hkx], hmo⟩
    · simp at hm
  | none =>
    right
    refine ⟨rfl, ?_⟩
    intro key hkey
    cases hmk : M !! key with
    | none => rfl
    | some o =>
      obtain ⟨x, hxm, hxo⟩ := hl.2 key o hmk
      have := (keyedItems_none KF xs ∅ k hx).2 x hxm
      rw [hk x hxm o hxo, hkd key o hmk, hkey] at this
      exact absurd rfl this

/-- **A relist's store step is the view's.** -/
theorem storeRel_replace (R : Reg) (KF : GoInterface → GoString) (σs : cache.St) (v : View)
    (xs : List GoInterface) (rvs : GoString) (M : GMap Key Obj) (n : Nat)
    (hrv : rvRel rvs (some n)) (hl : listRel R xs M)
    (hk : ∀ x ∈ xs, ∀ o, R !! x = some o → KF x = keyStr o.key)
    (hg : ∀ key, key ∈ M → keyGood key) (hkd : ∀ key o, M !! key = some o → o.key = key) :
    storeRel R (σs.replace (cache.keyedItems KF xs) rvs) (v.apply (.replaced M n)) :=
  ⟨hrv, itemsRel_keyed R KF xs M hl hk hg hkd⟩

/-- **A bookmark's store step is the view's.** -/
theorem storeRel_bookmark (R : Reg) (σs : cache.St) (v : View) (rvs : GoString) (n : Nat)
    (hR : storeRel R σs v) (hrv : rvRel rvs (some n)) :
    storeRel R (σs.bookmark rvs) (v.apply (.bookmark n)) := ⟨hrv, hR.2⟩

/-- The log's tables are keyed by their objects' keys. -/
theorem replay_keyed : ∀ (l : List Change) (M : GMap Key Obj),
    (∀ key o, M !! key = some o → o.key = key) →
    ∀ key o, (l.foldl applyChange M) !! key = some o → o.key = key
  | [], M, h => h
  | c :: l, M, h => by
    simp only [List.foldl_cons]
    apply replay_keyed l
    intro key o hk
    unfold applyChange at hk
    cases ht : c.typ with
    | deleted =>
      rw [ht, GMap.lookup_delete_iff] at hk
      split at hk
      · cases hk
      · exact h key o hk
    | added | modified =>
      rw [ht, GMap.lookup_insert_eq_iff] at hk
      split at hk
      · rename_i he; simp only [Option.some.injEq] at hk; subst hk; exact he
      · exact h key o hk

theorem tableAt_keyed (l : List Change) (v : Nat) :
    ∀ key o, (tableAt l v) !! key = some o → o.key = key :=
  replay_keyed _ ∅ (by intro key o h; simp at h)

theorem forall₂_append_split {α β : Type _} {R : α → β → Prop} :
    ∀ (l1 l2 : List α) (m : List β), List.Forall₂ R (l1 ++ l2) m →
      ∃ m1 m2, m = m1 ++ m2 ∧ List.Forall₂ R l1 m1 ∧ List.Forall₂ R l2 m2
  | [], l2, m, h => ⟨[], m, rfl, .nil, h⟩
  | a :: l1, l2, m, h => by
    cases h with
    | cons hab hrest =>
      obtain ⟨m1, m2, rfl, h1, h2⟩ := forall₂_append_split l1 l2 _ hrest
      exact ⟨_ :: m1, m2, rfl, .cons hab h1, h2⟩

theorem forall₂_nil_left {α β : Type _} {R : α → β → Prop} {m : List β}
    (h : List.Forall₂ R [] m) : m = [] := by cases h; rfl

theorem forall₂_length {α β : Type _} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → l.length = m.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [forall₂_length h]

/-- The key function the registry gives (the store's key string of a registered object). -/
def regKF (R : Reg) (x : GoInterface) : GoString :=
  match R !! x with
  | some o => keyStr o.key
  | none => []

/-- The resource version the registry gives (a registered object's). -/
def regRv (R : Reg) (x : GoInterface) : Option GoString :=
  (R !! x).map (fun o => o.meta.ResourceVersion')

/-- **The store step of popped deltas**: a lone delta's (`processDeltas`, `PopBatch`'s single
processing), a batch's (`processDeltasInBatch`). -/
def popStep (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString) (σ : cache.St) :
    List cache.FD → cache.St
  | [d] => cache.storeStepFD KF rvOf σ d
  | ds => cache.batchStore KF rvOf σ ds

/-- The popped deltas' relation: not yet applied, they are the abstract popped ones; applied, none is
left and the store is in the step's image (so a repeated write changes nothing). -/
def poppedRel (R : Reg) (σs : cache.St) (pd : List cache.FD) (ap : Bool) (popped : List Delta) :
    Prop :=
  if ap then popped = [] ∧ ∃ σ0, σs = popStep (regKF R) (regRv R) σ0 pd
  else List.Forall₂ (fdRel R) pd popped

/-- A version as a number (`none`: `0`), for the lower bound. -/
def rvNat : Option Nat → Nat
  | none => 0
  | some v => v

/-- The objects of a batch. -/
def fdObjs (ds : List cache.FD) : List GoInterface := ds.map cache.FD.obj?

theorem fdItems_congr (KF KF' : GoInterface → GoString) :
    ∀ (ds : List cache.FD) (it : cache.Items), (∀ x ∈ fdObjs ds, KF x = KF' x) →
      ds.foldl (cache.fdItems KF) it = ds.foldl (cache.fdItems KF') it
  | [], _, _ => rfl
  | d :: ds, it, h => by
    simp only [List.foldl_cons]
    have hd : cache.fdItems KF it d = cache.fdItems KF' it d := by
      cases d with
      | obj t o =>
        have := h o (by simp [fdObjs, cache.FD.obj?])
        simp only [cache.fdItems, this]
      | replaced _ _ => rfl
      | bookmark _ => rfl
    rw [hd]
    exact fdItems_congr KF KF' ds _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **A batch's store step depends on the key function and the versions at its objects only.** -/
theorem batchStore_congr (KF KF' : GoInterface → GoString) (rvOf rvOf' : GoInterface → Option GoString)
    (σ : cache.St) (ds : List cache.FD) (hk : ∀ x ∈ fdObjs ds, KF x = KF' x)
    (hr : ∀ x ∈ fdObjs ds, rvOf x = rvOf' x) :
    cache.batchStore KF rvOf σ ds = cache.batchStore KF' rvOf' σ ds := by
  unfold cache.batchStore
  cases hl : ds.getLast? with
  | none => rfl
  | some d =>
    simp only
    rw [fdItems_congr KF KF' ds σ.items hk]
    have hm : d.obj? ∈ fdObjs ds := List.mem_map.2 ⟨d, List.mem_of_getLast? hl, rfl⟩
    rw [hr _ hm]

/-- **A related batch of watch changes is a store batch** (`objOk`), its keys good and its objects'
versions their changes'. -/
theorem objOk_of_fdRel (R R0 : Reg) (hR0 : ∀ x o, R0 !! x = some o → R !! x = some o)
    (ds : List cache.FD) (abs : List Delta) (h : List.Forall₂ (fdRel R) ds abs)
    (hreg : ∀ x ∈ fdObjs ds, ∃ o, R0 !! x = some o)
    (hchg : ∀ a ∈ abs, ∃ c, a = .change c ∧ keyGood c.obj.key ∧
      c.obj.meta.ResourceVersion' = rvStr c.rv) :
    List.Forall₂ (objOk R (regKF R0) (regRv R0)) ds abs := by
  induction h with
  | nil => exact .nil
  | @cons fd a ds' abs' hfa hrest ih =>
    refine .cons ?_ (ih (fun x hx => hreg x (List.mem_cons_of_mem _ hx))
      (fun a ha => hchg a (List.mem_cons_of_mem _ ha)))
    obtain ⟨c, rfl, hgood, hrv⟩ := hchg a List.mem_cons_self
    cases fd with
    | obj t x =>
      obtain ⟨ht, hx, hnil⟩ := hfa
      obtain ⟨o, ho⟩ := hreg x (by simp [fdObjs, cache.FD.obj?])
      have hoc : o = c.obj := by
        have := hR0 x o ho; rw [hx] at this; cases this; rfl
      subst hoc
      refine ⟨x, c, by rw [ht], rfl, hx, ?_, hgood, ?_, hnil⟩
      · simp [regKF, ho]
      · simp [regRv, ho, hrv]
    | replaced _ _ => exact absurd hfa id
    | bookmark _ => exact absurd hfa id

theorem popStep_batch (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString)
    (σ : cache.St) (ds : List cache.FD) (h : 2 ≤ ds.length) :
    popStep KF rvOf σ ds = cache.batchStore KF rvOf σ ds := by
  match ds, h with
  | _ :: _ :: _, _ => rfl

theorem rvNat_mono {a b : Option Nat} (h : rvLe a b) : rvNat a ≤ rvNat b := by
  cases a <;> cases b <;> simp_all [rvLe, rvNat]

theorem fdRel_obj_changes (R : Reg) (ds : List cache.FD) (abs : List Delta)
    (h : List.Forall₂ (fdRel R) ds abs) (hobj : ∀ d ∈ ds, ∃ t x, d = .obj t x) :
    ∀ a ∈ abs, ∃ c, a = .change c := by
  induction h with
  | nil => intro a ha; simp at ha
  | @cons d a' ds' abs' hda hrest ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · obtain ⟨t, x, rfl⟩ := hobj d List.mem_cons_self
      cases a with
      | change c => exact ⟨c, rfl⟩
      | replaced _ _ => exact absurd hda id
      | bookmark _ => exact absurd hda id
    · exact ih (fun d hd => hobj d (List.mem_cons_of_mem _ hd)) a ha

/-- **The FIFO's queue and the popped batch**: an unpopulated queue holds bookmarks only (every
other delta populates it); a popped batch of several deltas was popped from a populated queue and
does not outnumber the initial items left (what `PopBatch`'s deferred step needs). -/
def fqOk (q : cache.FQ) (pd : List cache.FD) : Prop :=
  (q.populated = false → ∀ d ∈ q.items, ∃ rv, d = .bookmark rv) ∧
  (2 ≤ pd.length → q.populated = true ∧ (q.initCount = 0 ∨ pd.length ≤ q.initCount))

theorem batch_len_le (q : cache.FQ) (h : 0 < q.initCount) : q.batch.length ≤ q.initCount := by
  unfold cache.FQ.batch
  cases hq : q.items with
  | nil => simp
  | cons d ds =>
    simp only
    split
    · calc _ ≤ ((d :: ds).take (min 1000 q.initCount)).length := (List.takeWhile_prefix _).length_le
        _ ≤ min 1000 q.initCount := List.length_take_le _ _
        _ ≤ q.initCount := Nat.min_le_right _ _
    · simp; omega

/-- A batch of several deltas is of batchable ones. -/
theorem batch_batchable (q : cache.FQ) (h : 2 ≤ q.batch.length) :
    ∀ d ∈ q.batch, d.batchable = true := by
  unfold cache.FQ.batch at h ⊢
  cases hq : q.items with
  | nil => rw [hq] at h; simp at h
  | cons d ds =>
    rw [hq] at h
    simp only at h ⊢
    split
    · intro x hx
      exact List.all_eq_true.1 List.all_takeWhile x hx
    · rename_i hnb; simp only [hnb, Bool.false_eq_true, ↓reduceIte, List.length_singleton] at h
      omega

theorem batchable_obj (d : cache.FD) (h : d.batchable = true) : ∃ t x, d = .obj t x := by
  cases d with
  | obj t x => exact ⟨t, x, rfl⟩
  | replaced _ _ => simp [cache.FD.batchable] at h
  | bookmark _ => simp [cache.FD.batchable] at h

theorem fqOk_pop (q : cache.FQ) (h : fqOk q []) (hne : q.items ≠ []) :
    fqOk { q with items := q.items.drop q.batch.length } q.batch := by
  obtain ⟨h1, -⟩ := h
  refine ⟨fun hp d hd => h1 hp d (List.mem_of_mem_drop hd), fun hlen => ?_⟩
  have hpop : q.populated = true := by
    cases hp : q.populated with
    | true => rfl
    | false =>
      exfalso
      have hb := batch_batchable q hlen
      obtain ⟨d, ds, hds⟩ := List.exists_cons_of_ne_nil hne
      have hd : d ∈ q.batch := by
        unfold cache.FQ.batch; rw [hds]; simp only
        split
        · rename_i hb'
          have : 0 < (if 0 < q.initCount then min 1000 q.initCount else 1000) := by split <;> omega
          obtain ⟨n, hn⟩ : ∃ n, (if 0 < q.initCount then min 1000 q.initCount else 1000) = n + 1 :=
            ⟨_, (Nat.succ_pred_eq_of_pos this).symm⟩
          rw [hn]; simp [hb']
        · simp
      obtain ⟨rv, hrv⟩ := h1 hp d (by rw [hds]; exact List.mem_cons_self)
      have := hb d hd
      rw [hrv] at this
      simp [cache.FD.batchable] at this
  refine ⟨hpop, ?_⟩
  by_cases h0 : q.initCount = 0
  · exact Or.inl h0
  · exact Or.inr (batch_len_le q (by omega))

/-- **One popped delta's store step is the view's.** -/
theorem storeRel_single (R R0 : Reg) (hsub : ∀ x o, R0 !! x = some o → R !! x = some o)
    (σs : cache.St) (v : View) (d : cache.FD) (a : Delta) (hR : storeRel R σs v)
    (hfd : fdRel R d a) (hreg : ∀ x ∈ d.objs, ∃ o, R0 !! x = some o)
    (hchg : ∀ c, a = .change c → keyGood c.obj.key ∧ c.obj.meta.ResourceVersion' = rvStr c.rv)
    (hrep : ∀ M n, a = .replaced M n →
      (∀ key, key ∈ M → keyGood key) ∧ (∀ key o, M !! key = some o → o.key = key)) :
    storeRel R (cache.storeStepFD (regKF R0) (regRv R0) σs d) (v.apply a) := by
  cases d with
  | obj t x =>
    cases a with
    | change c =>
      obtain ⟨rfl, hx, hnil⟩ := hfd
      obtain ⟨o, ho⟩ := hreg x (by simp [cache.FD.objs])
      have hoc : o = c.obj := by have := hsub x o ho; rw [hx] at this; cases this; rfl
      subst hoc
      obtain ⟨hgood, hrv⟩ := hchg _ rfl
      exact storeRel_change R _ _ σs v _ x hR hx (by simp [regKF, ho]) hgood
        (by simp [regRv, ho, hrv]) hnil
    | replaced _ _ => exact absurd hfd id
    | bookmark _ => exact absurd hfd id
  | replaced xs rvs =>
    cases a with
    | replaced M n =>
      obtain ⟨hrv, hl⟩ := hfd
      obtain ⟨hg, hkd⟩ := hrep M n rfl
      refine storeRel_replace R (regKF R0) σs v xs rvs M n hrv hl ?_ hg hkd
      intro x hx o hxo
      obtain ⟨o', ho'⟩ := hreg x (by simpa [cache.FD.objs] using hx)
      have : o' = o := by have := hsub x o' ho'; rw [hxo] at this; cases this; rfl
      subst this
      simp [regKF, ho']
    | change _ => exact absurd hfd id
    | bookmark _ => exact absurd hfd id
  | bookmark rvs =>
    cases a with
    | bookmark n => exact storeRel_bookmark R σs v rvs n hR hfd
    | change _ => exact absurd hfd id
    | replaced _ _ => exact absurd hfd id

/-- The keys of the log's tables are good when the log's are. -/
theorem replay_good : ∀ (l : List Change) (M : GMap Key Obj),
    (∀ key, key ∈ M → keyGood key) → (∀ c ∈ l, keyGood c.obj.key) →
    ∀ key, key ∈ l.foldl applyChange M → keyGood key
  | [], M, h, _ => h
  | c :: l, M, h, hl => by
    simp only [List.foldl_cons]
    apply replay_good l
    · intro key hk
      unfold applyChange at hk
      cases ht : c.typ with
      | deleted =>
        rw [ht, GMap.mem_iff, GMap.lookup_delete_iff] at hk
        split at hk
        · simp at hk
        · exact h key hk
      | added | modified =>
        rw [ht, GMap.mem_iff, GMap.lookup_insert_eq_iff] at hk
        split at hk
        · rename_i he; rw [← he]; exact hl c List.mem_cons_self
        · exact h key hk
    · exact fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')

theorem tableAt_good (l : List Change) (v : Nat) (hl : ∀ c ∈ l, keyGood c.obj.key) :
    ∀ key, key ∈ tableAt l v → keyGood key :=
  replay_good _ ∅ (by intro key h; simp [GMap.mem_iff] at h)
    (fun c hc => hl c (List.mem_filter.1 hc).1)

theorem storeStepFD_congr (KF KF' : GoInterface → GoString) (rvOf rvOf' : GoInterface → Option GoString)
    (σ : cache.St) (d : cache.FD) (hk : ∀ x ∈ d.objs, KF x = KF' x)
    (hr : ∀ x ∈ d.objs, rvOf x = rvOf' x) :
    cache.storeStepFD KF rvOf σ d = cache.storeStepFD KF' rvOf' σ d := by
  cases d with
  | obj t o =>
    have h1 := hk o (by simp [cache.FD.objs])
    have h2 := hr o (by simp [cache.FD.objs])
    simp only [cache.storeStepFD, cache.rvOfObj, h1, h2]
  | replaced xs rv =>
    simp only [cache.storeStepFD]
    congr 1
    unfold cache.keyedItems
    have : ∀ (ys : List GoInterface) (m : cache.Items), (∀ y ∈ ys, KF y = KF' y) →
        ys.foldl (fun m x => <[KF x := x]> m) m = ys.foldl (fun m x => <[KF' x := x]> m) m := by
      intro ys
      induction ys with
      | nil => intro _ _; rfl
      | cons y ys ih =>
        intro m h
        simp only [List.foldl_cons, h y List.mem_cons_self]
        exact ih _ (fun z hz => h z (List.mem_cons_of_mem _ hz))
    exact this xs ∅ (fun y hy => hk y (by simpa [cache.FD.objs] using hy))
  | bookmark _ => rfl

theorem forall₂_singleton {α β : Type _} {R : α → β → Prop} {a : α} {l : List β}
    (h : List.Forall₂ R [a] l) : ∃ b, l = [b] ∧ R a b := by
  cases h with
  | cons hab hrest => cases hrest; exact ⟨_, rfl, hab⟩

/-! ### The registry grows -/

/-- `R'` extends `R`. -/
def regLe (R R' : Reg) : Prop := ∀ x o, R !! x = some o → R' !! x = some o

theorem fdRel_mono {R R' : Reg} (h : regLe R R') (d : cache.FD) (a : Delta) (hd : fdRel R d a) :
    fdRel R' d a := by
  cases d with
  | obj t x =>
    cases a with
    | change c => exact ⟨hd.1, h _ _ hd.2.1, hd.2.2⟩
    | _ => exact absurd hd id
  | replaced xs rvs =>
    cases a with
    | replaced M n =>
      obtain ⟨hrv, h1, h2⟩ := hd
      refine ⟨hrv, fun x hx => ?_, fun key o ho => ?_⟩
      · obtain ⟨o, ho, hm⟩ := h1 x hx; exact ⟨o, h _ _ ho, hm⟩
      · obtain ⟨x, hx, hxo⟩ := h2 key o ho; exact ⟨x, hx, h _ _ hxo⟩
    | _ => exact absurd hd id
  | bookmark rvs =>
    cases a with
    | bookmark n => exact hd
    | _ => exact absurd hd id

theorem forall₂_fdRel_mono {R R' : Reg} (h : regLe R R') {ds : List cache.FD} {abs : List Delta}
    (hd : List.Forall₂ (fdRel R) ds abs) : List.Forall₂ (fdRel R') ds abs := by
  induction hd with
  | nil => exact .nil
  | cons h1 _ ih => exact .cons (fdRel_mono h _ _ h1) ih

theorem storeRel_mono {R R' : Reg} (h : regLe R R') (σs : cache.St) (v : View)
    (hR : storeRel R σs v) : storeRel R' σs v := by
  obtain ⟨hrv, hg, hkd, hit⟩ := hR
  refine ⟨hrv, hg, hkd, fun k => ?_⟩
  rcases hit k with ⟨x, o, hx, hro, hko, hvo⟩ | hn
  · exact Or.inl ⟨x, o, hx, h _ _ hro, hko, hvo⟩
  · exact Or.inr hn

/-- The objects of the popped deltas are registered (and a batch of several is of object
deltas). -/
def pdReg (R : Reg) (pd : List cache.FD) : Prop :=
  (∀ d ∈ pd, ∀ x ∈ d.objs, ∃ o, R !! x = some o) ∧ (2 ≤ pd.length → ∀ d ∈ pd, ∃ t x, d = .obj t x)

theorem regKF_mono {R R' : Reg} (h : regLe R R') (x : GoInterface) (hx : ∃ o, R !! x = some o) :
    regKF R x = regKF R' x := by
  obtain ⟨o, ho⟩ := hx; simp [regKF, ho, h x o ho]

theorem regRv_mono {R R' : Reg} (h : regLe R R') (x : GoInterface) (hx : ∃ o, R !! x = some o) :
    regRv R x = regRv R' x := by
  obtain ⟨o, ho⟩ := hx; simp [regRv, ho, h x o ho]

theorem fdObjs_objs (ds : List cache.FD) (hobj : ∀ d ∈ ds, ∃ t x, d = .obj t x)
    (x : GoInterface) (hx : x ∈ fdObjs ds) : ∃ d ∈ ds, x ∈ d.objs := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
  obtain ⟨t, y, rfl⟩ := hobj _ hd
  exact ⟨_, hd, by simp [cache.FD.obj?, cache.FD.objs]⟩

theorem popStep_mono {R R' : Reg} (h : regLe R R') (σ : cache.St) (pd : List cache.FD)
    (hreg : pdReg R pd) : popStep (regKF R) (regRv R) σ pd = popStep (regKF R') (regRv R') σ pd := by
  match pd with
  | [d] =>
    exact storeStepFD_congr _ _ _ _ σ d (fun x hx => regKF_mono h x (hreg.1 d (by simp) x hx))
      (fun x hx => regRv_mono h x (hreg.1 d (by simp) x hx))
  | [] => rfl
  | d1 :: d2 :: ds =>
    rw [popStep_batch _ _ _ _ (by simp), popStep_batch _ _ _ _ (by simp)]
    have hobj := hreg.2 (by simp)
    exact batchStore_congr _ _ _ _ σ _ (fun x hx => by
        obtain ⟨d, hd, hxd⟩ := fdObjs_objs _ hobj x hx
        exact regKF_mono h x (hreg.1 d hd x hxd))
      (fun x hx => by
        obtain ⟨d, hd, hxd⟩ := fdObjs_objs _ hobj x hx
        exact regRv_mono h x (hreg.1 d hd x hxd))

theorem poppedRel_mono {R R' : Reg} (h : regLe R R') (σs : cache.St) (pd : List cache.FD)
    (ap : Bool) (popped : List Delta) (hreg : pdReg R pd) (hp : poppedRel R σs pd ap popped) :
    poppedRel R' σs pd ap popped := by
  unfold poppedRel at hp ⊢
  cases ap with
  | true =>
    simp only [↓reduceIte] at hp ⊢
    obtain ⟨h1, σ0, h2⟩ := hp
    exact ⟨h1, σ0, by rw [h2, popStep_mono h σ0 pd hreg]⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
    exact forall₂_fdRel_mono h hp

theorem fdRel_reg (R : Reg) (ds : List cache.FD) (abs : List Delta)
    (h : List.Forall₂ (fdRel R) ds abs) : ∀ d ∈ ds, ∀ x ∈ d.objs, ∃ o, R !! x = some o := by
  induction h with
  | nil => intro d hd; simp at hd
  | @cons d a ds' abs' hda hrest ih =>
    intro d' hd' x hx
    rcases List.mem_cons.1 hd' with rfl | hd'
    · cases d' with
      | obj t y =>
        cases a with
        | change c =>
          simp only [cache.FD.objs, List.mem_singleton] at hx
          subst hx; exact ⟨_, hda.2.1⟩
        | _ => exact absurd hda id
      | replaced xs rvs =>
        cases a with
        | replaced M n =>
          obtain ⟨o, ho, -⟩ := hda.2.1 x (by simpa [cache.FD.objs] using hx)
          exact ⟨o, ho⟩
        | _ => exact absurd hda id
      | bookmark _ => simp [cache.FD.objs] at hx
    · exact ih d' hd' x hx

theorem pdReg_batch (R : Reg) (q : cache.FQ) (abs : List Delta)
    (h : List.Forall₂ (fdRel R) q.batch abs) : pdReg R q.batch :=
  ⟨fdRel_reg R _ abs h, fun hlen d hd => batchable_obj d (batch_batchable q hlen d hd)⟩

theorem regLe_insert (R : Reg) (x : GoInterface) (o : Obj) (h : R !! x = none) :
    regLe R (<[x := o]> R) := by
  intro y o' hy
  rw [GMap.lookup_insert_eq_iff]
  by_cases he : x = y
  · subst he; rw [h] at hy; cases hy
  · simp [he, hy]

theorem pdReg_mono {R R' : Reg} (h : regLe R R') (pd : List cache.FD) (hp : pdReg R pd) :
    pdReg R' pd :=
  ⟨fun d hd x hx => by obtain ⟨o, ho⟩ := hp.1 d hd x hx; exact ⟨o, h _ _ ho⟩, hp.2⟩

theorem forall₂_snoc {α β : Type _} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β} {a : α} {b : β}, List.Forall₂ R l m → R a b →
      List.Forall₂ R (l ++ [a]) (m ++ [b])
  | _, _, _, _, .nil, h => .cons h .nil
  | _, _, _, _, .cons h1 h2, h => .cons h1 (forall₂_snoc h2 h)

end model

end informer
end EtcdGrove
end Perennial
