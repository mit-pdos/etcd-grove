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
  | .obj t x, .change c => t = fdTypeOf c.typ ∧ R !! x = some c.obj
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

end model

end informer
end EtcdGrove
end Perennial
