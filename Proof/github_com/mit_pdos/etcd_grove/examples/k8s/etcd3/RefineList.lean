/-
Lean-first (no Rocq counterpart).

# The store's lists refine the driver's (stage 7e-3c of `notes/k8s-7e-scope.md`)

`refine_list` (`notes/k8s-7e-2-draft.md` §8, with its "Corrections (2026-11-09)" R1-R4): on related
states, the driver's `mlistL` answers what the driver's `listOut` makes of the store's list answer
(`store.GetList.spec`'s `listIs` over `kListL`), or `ETooLarge` exactly when the store's is too
large.

- `ItemRelH ki it`: a store item (`Model.lean`'s `KItem`, decoded from etcd) and a driver item
  agree: the driver's object is the store's object at the item's resource version, and the
  canonical bits agree (the whole object, correction R4; 7e-4 adopts it);
- `KRelS s rv g`: etcd's store `s` at revision `rv` (through `absK` under the store's prefix
  `/registry/objs`) and the driver's store `g` agree at every name, `g` sorted, the same revision;
- `KRelH h σ`: the driver's state (its store and history) and etcd's state `σ` agree at the current
  revision and at every revision `1..σ.rev`, `σ.rev < 2^63`, every mod revision below `2^63`;
- `listOutDriver x R a`: the driver's `listOut` of the list `listIs` describes (the items at their
  mod revisions, the list's resource version `R`, the token and the remaining count iff more).

The proof: under `KRelS`, the driver's items in scope (`scopeL`) are the store's in-scope decoded
key-values (`kListL`'s list) with the keys' `/registry` dropped and the objects at their mod
revisions (`scopeL_eq`: both strictly sorted with the same members), and the loop commutes with that
map (`loop_map`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ItemList
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.TxnModelKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

/-! ## The loop, generically -/

namespace ListModel

variable {α β O P : Type} [DecidableEq α] [DecidableEq β]

/-- One step commutes with a map of the keys and the values. -/
theorem lstep_map (kf : List α → List β) (vf : O → P) (sel : P → Bool) (lim : Nat)
    (s : LState α O) (ko : List α × O) :
    lstep sel lim ⟨s.items.map vf, s.last.map kf, s.more, s.total⟩ (kf ko.1, vf ko.2) =
      ⟨(lstep (fun o => sel (vf o)) lim s ko).items.map vf,
        (lstep (fun o => sel (vf o)) lim s ko).last.map kf,
        (lstep (fun o => sel (vf o)) lim s ko).more,
        (lstep (fun o => sel (vf o)) lim s ko).total⟩ := by
  unfold lstep
  simp only [List.length_map]
  by_cases h1 : 0 < lim ∧ lim ≤ s.items.length
  · simp [h1]
  · by_cases h2 : sel (vf ko.2) = true
    · simp [h1, h2]
    · simp [h1, h2]

theorem foldl_map (kf : List α → List β) (vf : O → P) (sel : P → Bool) (lim : Nat) :
    ∀ (l : List (List α × O)) (s : LState α O),
      (l.map fun ko => (kf ko.1, vf ko.2)).foldl (lstep sel lim)
          ⟨s.items.map vf, s.last.map kf, s.more, s.total⟩ =
        ⟨(l.foldl (lstep (fun o => sel (vf o)) lim) s).items.map vf,
          (l.foldl (lstep (fun o => sel (vf o)) lim) s).last.map kf,
          (l.foldl (lstep (fun o => sel (vf o)) lim) s).more,
          (l.foldl (lstep (fun o => sel (vf o)) lim) s).total⟩
  | [], s => rfl
  | ko :: l, s => by
    simp only [List.map_cons, List.foldl_cons]
    rw [lstep_map kf vf sel lim s ko]
    exact foldl_map kf vf sel lim l _

/-- **The loop commutes with a map** of the keys and the values. -/
theorem loop_map (kf : List α → List β) (vf : O → P) (sel : P → Bool) (lim : Nat)
    (l : List (List α × O)) :
    loop sel lim (l.map fun ko => (kf ko.1, vf ko.2)) =
      ⟨(loop (fun o => sel (vf o)) lim l).items.map vf,
        (loop (fun o => sel (vf o)) lim l).last.map kf,
        (loop (fun o => sel (vf o)) lim l).more,
        (loop (fun o => sel (vf o)) lim l).total⟩ :=
  foldl_map kf vf sel lim l ⟨[], none, false, 0⟩

/-- The loop's last key is the start's, or a key of the list. -/
theorem foldl_last (sel : O → Bool) (lim : Nat) :
    ∀ (l : List (List α × O)) (s : LState α O),
      (l.foldl (lstep sel lim) s).last = s.last ∨
        ∃ ko ∈ l, (l.foldl (lstep sel lim) s).last = some ko.1
  | [], s => Or.inl rfl
  | ko :: l, s => by
    simp only [List.foldl_cons]
    rcases foldl_last sel lim l (lstep sel lim s ko) with h | ⟨ko', hm, h⟩
    · rw [h]
      simp only [lstep]
      by_cases h1 : 0 < lim ∧ lim ≤ s.items.length
      · simp [h1]
      · by_cases h2 : sel ko.2 = true
        · exact Or.inr ⟨ko, List.mem_cons_self, by simp [h1, h2]⟩
        · simp [h1, h2]
    · exact Or.inr ⟨ko', List.mem_cons_of_mem _ hm, h⟩

theorem loop_last (sel : O → Bool) (lim : Nat) (l : List (List α × O)) (k : List α)
    (h : (loop sel lim l).last = some k) : ∃ ko ∈ l, ko.1 = k := by
  rcases foldl_last sel lim l ⟨[], none, false, 0⟩ with h' | ⟨ko, hm, h'⟩
  · unfold loop at h; rw [h'] at h; cases h
  · unfold loop at h; rw [h'] at h; exact ⟨ko, hm, Option.some.inj h⟩

/-- A list of at most one item has no more. -/
theorem loop_more_short (sel : O → Bool) (lim : Nat) (l : List (List α × O)) (hl : l.length ≤ 1) :
    (loop sel lim l).more = false := by
  match l, hl with
  | [], _ => rfl
  | [ko], _ =>
    unfold loop
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    split
    · rename_i h; simp at h; omega
    · split <;> rfl

/-- The loop's state: `more` only with items, items only with a last key. -/
def StOk (s : LState α O) : Prop := (s.more = true → s.items ≠ []) ∧ (s.items ≠ [] → s.last.isSome)

theorem foldl_stOk (sel : O → Bool) (lim : Nat) :
    ∀ (l : List (List α × O)) (s : LState α O), StOk s → StOk (l.foldl (lstep sel lim) s)
  | [], s, h => h
  | ko :: l, s, h => by
    simp only [List.foldl_cons]
    apply foldl_stOk sel lim l
    obtain ⟨h1, h2⟩ := h
    simp only [lstep]
    by_cases hc : 0 < lim ∧ lim ≤ s.items.length
    · simp only [hc, and_self, ite_true]
      refine ⟨fun _ => ?_, h2⟩
      intro he; rw [he] at hc; simp at hc; omega
    · simp only [hc, ite_false]
      by_cases hs : sel ko.2 = true
      · simp only [hs, ite_true]; exact ⟨fun _ => by simp, fun _ => rfl⟩
      · simp only [hs]; exact ⟨h1, h2⟩

/-- **A list with more has a last key.** -/
theorem loop_more_last (sel : O → Bool) (lim : Nat) (l : List (List α × O))
    (h : (loop sel lim l).more = true) : ∃ k, (loop sel lim l).last = some k := by
  have hok := foldl_stOk sel lim l ⟨[], none, false, 0⟩ ⟨by simp, by simp⟩
  obtain ⟨h1, h2⟩ := hok
  exact Option.isSome_iff_exists.1 (h2 (h1 h))

end ListModel

/-! ## Strings with a common prefix, sorted lists -/

theorem goStringLt_append_left_iff (p a b : GoString) :
    go.GoStringLt (p ++ a) (p ++ b) ↔ go.GoStringLt a b := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    rw [List.cons_append, List.cons_append, go.goStringLt_cons_iff]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact absurd h (Int.lt_irrefl _)
      · exact ih.1 h
    · intro h; exact Or.inr ⟨rfl, ih.2 h⟩

/-- **Two lists strictly sorted by key with the same members are equal.** -/
theorem eq_of_sorted_mem {V : Type} :
    ∀ (l l' : List (GoString × V)), (l.map Prod.fst).Pairwise go.GoStringLt →
      (l'.map Prod.fst).Pairwise go.GoStringLt → (∀ e, e ∈ l ↔ e ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], e :: _, _, _, h => absurd ((h e).2 List.mem_cons_self) (List.not_mem_nil)
  | e :: _, [], _, _, h => absurd ((h e).1 List.mem_cons_self) (List.not_mem_nil)
  | e :: l, e' :: l', hs, hs', h => by
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hs hs'
    have he : e = e' := by
      rcases List.mem_cons.1 ((h e).1 List.mem_cons_self) with he | he
      · exact he
      rcases List.mem_cons.1 ((h e').2 List.mem_cons_self) with he' | he'
      · exact he'.symm
      have h1 := hs'.1 e.1 ⟨e, he, rfl⟩
      have h2 := hs.1 e'.1 ⟨e', he', rfl⟩
      exact absurd h2 (go.goStringLt_asymm h1)
    subst he
    congr 1
    apply eq_of_sorted_mem l l' hs.2 hs'.2
    intro x
    have hx := h x
    constructor
    · intro hm
      rcases List.mem_cons.1 (hx.1 (List.mem_cons_of_mem _ hm)) with rfl | hm'
      · exact absurd (hs.1 x.1 ⟨x, hm, rfl⟩) (go.goStringLt_irrefl _)
      · exact hm'
    · intro hm
      rcases List.mem_cons.1 (hx.2 (List.mem_cons_of_mem _ hm)) with rfl | hm'
      · exact absurd (hs'.1 x.1 ⟨x, hm, rfl⟩) (go.goStringLt_irrefl _)
      · exact hm'

section go
variable [GooseExts]

/-! ## The relation -/

/-- **A store item and a driver item agree** (the whole object, correction R4). -/
def ItemRelH (ki : KItem DObj) (it : item) : Prop :=
  it.obj' = ki.obj.toObj (W64 (ki.rv : Int)) ∧ ki.canon = it.canon'

/-- A store item and `lookupL`'s answer agree (both absent, or both present and related). -/
def PairRelH : Option (KItem DObj) → item × Bool → Prop
  | none, (_, false) => True
  | some ki, (it, true) => ItemRelH ki it
  | _, _ => False

/-- The store's prefix of the driver's keys (`Prefix + ResourcePrefix`). -/
abbrev kpfxD : GoString := go!"/registry/objs"

/-- **etcd's store `s` at revision `rv` and the driver's store `g`**: `g` sorted, the same
revision, and at every name the same item (`absK` under the store's prefix). -/
def KRelS (s : KVStore) (rv : Nat) (g : GSt) : Prop :=
  SortedI g.items ∧ W64 (rv : Int) = g.rv ∧
    ∀ n, PairRelH ((absK driverCodec.dec kpfxD ⟨linkv.absM s.kvs, rv⟩).items (mkeyL n))
      (lookupL g.items n)

/-- **The driver's state and etcd's** (correction R4): the store at the current revision, and the
history at every revision `1..σ.rev`; the revision and every mod revision below `2^63`. -/
def KRelH (h : HSt) (σ : KVState) : Prop :=
  σ.rev < 2 ^ 63 ∧ KRelS σ.store σ.rev h.st ∧
    (∀ r, 1 ≤ r → r ≤ σ.rev → KRelS (σ.at r) r (histAtL h.hist (W64 (r : Int)))) ∧
    ∀ r ≤ σ.rev, ∀ v ∈ (σ.at r).kvs, uint.Z v.modRev < 2 ^ 63

/-- What a list of `x` selects of a store object (`selOkL` reads no resource version). -/
def selD (x : Input) (o : DObj) : Bool := selOkL x (o.toObj (W64 0))

/-- **The driver's `listOut` of the store's list answer** (`listIs`): the items at their mod
revisions, the list's resource version `R`, the token (`encL` of the last match's key and `"\x00"`,
the prepared prefix and `R`) and the remaining count iff more. -/
def listOutDriver (x : Input) (R : w64) (a : ListModel.LState w8 (DObj × Nat)) : Output :=
  let kp := go!"/registry" ++ (prepareKeyM go!"/objs" x.ListKey' x.Recursive').getD []
  let its := encItemsL (a.items.reverse.map fun p => p.1.toObj (W64 (p.2 : Int)))
  if a.more then
    ⟨W64 0, [], 0, [], [], [], [], [], [], 0, its, R, encL (a.last.getD [] ++ [W8 0]) kp R,
      predEmptyL x, if predEmptyL x then W64 (a.total : Int) - x.Limit' else 0, [], false⟩
  else ⟨W64 0, [], 0, [], [], [], [], [], [], 0, its, R, [], false, 0, [], false⟩

/-! ## The scope -/

/-- The store's in-scope decoded key-values (`kListL`'s list). -/
def storeScope (kp : GoString) (r : Bool) (s : KVStore) : List (GoString × (DObj × Nat)) :=
  (s.kvs.filter fun v => kInScope kp r v.key).filterMap fun v =>
    (driverCodec.dec v.value).map fun d => (v.key, (d.1, sint.nat v.modRev))

/-- The driver's view of a store element: the key without `/registry`, the object at its revision. -/
def toDrv (e : GoString × (DObj × Nat)) : GoString × Obj :=
  (e.1.drop 9, e.2.1.toObj (W64 (e.2.2 : Int)))

/-- `PrepareKey`'s answer: the key, with `/` appended if recursive. -/
theorem prepareKeyM_eq (rp lk k : GoString) (r : Bool) (hk : prepareKeyM rp lk r = some k) :
    k = (if r = true ∧ ¬ go!"/" <:+ lk then lk ++ go!"/" else lk) := by
  unfold prepareKeyM at hk
  split at hk
  · simp at hk
  split at hk
  · simp at hk
  split at hk
  · simp at hk
  split at hk
  · rename_i hc
    simp only [hc]
    simp at hk
    exact hk.2.symm
  · rename_i hc
    simp only [hc, ite_false]
    simp at hk
    exact hk.2.symm

theorem prepareKeyM_scope (lk k : GoString) (r : Bool) (hk : prepareKeyM go!"/objs" lk r = some k)
    (sk : GoString) : kInScope (go!"/registry" ++ k) r (go!"/registry" ++ sk) =
      keyInScopeL lk r sk := by
  have hk := prepareKeyM_eq _ _ _ _ hk
  subst hk
  unfold kInScope keyInScopeL
  cases r
  · simp
  · simp only [ite_true]
    have : (if True ∧ ¬ go!"/" <:+ lk then lk ++ go!"/" else lk) = trimSufL lk go!"/" ++ go!"/" := by
      unfold trimSufL
      by_cases hs : go!"/" <:+ lk
      · obtain ⟨t, rfl⟩ := hs
        simp
      · simp [hs]
    rw [this]
    simp only [decide_eq_decide]
    exact List.prefix_append_right_inj _

theorem prepareKeyM_objs (lk k : GoString) (r : Bool) (hk : prepareKeyM go!"/objs" lk r = some k)
    (hlk : go!"/objs/" <+: lk) : go!"/objs/" <+: k := by
  have hk := prepareKeyM_eq _ _ _ _ hk
  subst hk
  split
  · exact hlk.trans (List.prefix_append _ _)
  · exact hlk

/-! ## The two scopes are the same list -/

theorem sint_nat_of_lt (m : w64) (h : uint.Z m < 2 ^ 63) : sint.nat m = uint.nat m := by
  simp only [sint.nat, uint.Z, uint.nat] at *
  rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  simp

theorem kInScope_registry (k key : GoString) (r : Bool) (h : kInScope (go!"/registry" ++ k) r key) :
    (go!"/registry" ++ k) <+: key := by
  unfold kInScope at h
  cases r
  · simp only [Bool.false_eq_true, ite_false, decide_eq_true_eq] at h; rw [h]; exact List.prefix_refl _
  · simpa using h

theorem drop_registry (t : GoString) : (go!"/registry" ++ t).drop 9 = t := by
  exact List.drop_left' rfl

/-- The store's items under `absK` at a driver name: the key-value at its key, decoded. -/
theorem absK_mkeyL (s : KVStore) (rv : Nat) (n : GoString) :
    (absK driverCodec.dec kpfxD ⟨linkv.absM s.kvs, rv⟩).items (mkeyL n) =
      (mvcc.findKey (mkeyL n) s.kvs).bind fun v =>
        (driverCodec.dec v.value).map fun oc => ⟨oc.1, uint.nat v.modRev, oc.2⟩ := by
  have hp : kpfxD <+: mkeyL n := ⟨go!"/" ++ n, rfl⟩
  simp only [absK, hp, ite_true, linkv.absM]
  cases mvcc.findKey (mkeyL n) s.kvs <;> rfl

/-- In a sorted item list, a member is what its key looks up. -/
theorem lookupL_mem (its : List item) (hs : SortedI its) (it : item) (h : it ∈ its) :
    lookupL its it.key' = (it, true) := by
  have hf : its.find? (fun e => decide (e.key' = it.key')) = some it := by
    induction its with
    | nil => cases h
    | cons e es ih =>
      unfold SortedI at hs
      simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hs
      rw [List.find?_cons]
      rcases List.mem_cons.1 h with rfl | h'
      · simp
      · have hne : e.key' ≠ it.key' := fun he =>
          go.goStringLt_irrefl it.key' (he ▸ hs.1 it.key' ⟨it, h', rfl⟩)
        simp only [hne, decide_false]
        exact ih hs.2 h'
  unfold lookupL; rw [hf]

theorem lookupL_some (its : List item) (n : GoString) (it : item) (b : Bool)
    (h : lookupL its n = (it, b)) (hb : b = true) : it ∈ its ∧ it.key' = n := by
  subst hb
  unfold lookupL at h
  split at h
  · rename_i e he
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨List.mem_of_find?_eq_some he, by simpa using List.find?_some he⟩
  · simp at h

theorem storeKeyL_lt (a b : GoString) : go.GoStringLt (storeKeyL a) (storeKeyL b) ↔ go.GoStringLt a b :=
  goStringLt_append_left_iff _ _ _

theorem mem_scopeL (x : Input) (its : List item) (e : GoString × Obj) :
    e ∈ scopeL x its ↔ ∃ it ∈ its, keyInScopeL x.ListKey' x.Recursive' (storeKeyL it.key') = true ∧
      e = (storeKeyL it.key', it.obj') := by
  unfold scopeL
  simp only [List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨it, hit, rfl⟩, hs⟩; exact ⟨it, hit, hs, rfl⟩
  · rintro ⟨it, hit, hs, rfl⟩; exact ⟨⟨it, hit, rfl⟩, hs⟩

theorem mem_storeScope (kp : GoString) (r : Bool) (s : KVStore) (e : GoString × Obj) :
    e ∈ (storeScope kp r s).map toDrv ↔ ∃ v ∈ s.kvs, kInScope kp r v.key = true ∧
      ∃ d c, driverCodec.dec v.value = some (d, c) ∧
        e = (v.key.drop 9, d.toObj (W64 (sint.nat v.modRev : Int))) := by
  unfold storeScope toDrv
  simp only [List.mem_map, List.mem_filterMap, List.mem_filter, Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, ⟨v, ⟨hv, hsc⟩, ⟨d, c⟩, hd, rfl⟩, rfl⟩
    exact ⟨v, hv, hsc, d, c, hd, rfl⟩
  · rintro ⟨v, hv, hsc, d, c, hd, rfl⟩
    exact ⟨_, ⟨v, ⟨hv, hsc⟩, ⟨d, c⟩, hd, rfl⟩, rfl⟩

theorem scopeL_sorted (x : Input) (its : List item) (hs : SortedI its) :
    ((scopeL x its).map Prod.fst).Pairwise go.GoStringLt := by
  unfold scopeL
  have h1 : ((its.map fun it => (storeKeyL it.key', it.obj')).map Prod.fst).Pairwise go.GoStringLt := by
    unfold SortedI at hs
    simp only [List.map_map]
    rw [List.pairwise_map] at hs ⊢
    exact hs.imp fun h => (storeKeyL_lt _ _).2 h
  rw [List.pairwise_map] at h1 ⊢
  exact h1.filter _

theorem storeScope_sorted (k : GoString) (r : Bool) (s : KVStore) :
    (((storeScope (go!"/registry" ++ k) r s).map toDrv).map Prod.fst).Pairwise go.GoStringLt := by
  have hs := KVStore.kvs_sorted s
  unfold storeScope toDrv
  rw [List.map_map, List.pairwise_map, List.pairwise_filterMap]
  have hf := hs.filter (fun v => kInScope (go!"/registry" ++ k) r v.key)
  refine List.Pairwise.imp_of_mem ?_ hf
  intro a b ha hb hab
  intro ea hea eb heb
  simp only [Option.map_eq_some_iff] at hea heb
  obtain ⟨_, -, rfl⟩ := hea
  obtain ⟨_, -, rfl⟩ := heb
  simp only [Function.comp]
  have ha' := kInScope_registry k a.key r (List.mem_filter.1 ha).2
  have hb' := kInScope_registry k b.key r (List.mem_filter.1 hb).2
  obtain ⟨ta, hta⟩ := (List.prefix_append go!"/registry" k).trans ha'
  obtain ⟨tb, htb⟩ := (List.prefix_append go!"/registry" k).trans hb'
  unfold etcdKvLess at hab
  rw [← hta, ← htb] at hab ⊢
  rw [drop_registry, drop_registry]
  exact (goStringLt_append_left_iff _ _ _).1 hab

/-- **The driver's items in scope are the store's** (under `KRelS`). -/
theorem scopeL_eq (x : Input) (k : GoString) (g : GSt) (s : KVStore) (rv : Nat)
    (hS : KRelS s rv g) (hmod : ∀ v ∈ s.kvs, uint.Z v.modRev < 2 ^ 63)
    (hk : prepareKeyM go!"/objs" x.ListKey' x.Recursive' = some k)
    (hlk : go!"/objs/" <+: x.ListKey') :
    scopeL x g.items = (storeScope (go!"/registry" ++ k) x.Recursive' s).map toDrv := by
  obtain ⟨hsort, -, hrel⟩ := hS
  have hsn : ∀ v ∈ s.kvs, sint.nat v.modRev = uint.nat v.modRev := fun v hv =>
    sint_nat_of_lt _ (hmod v hv)
  apply eq_of_sorted_mem _ _ (scopeL_sorted x g.items hsort) (storeScope_sorted k _ s)
  intro e
  rw [mem_scopeL, mem_storeScope]
  constructor
  · rintro ⟨it, hit, hsc, rfl⟩
    have hl := lookupL_mem g.items hsort it hit
    have hr := hrel it.key'
    rw [hl, absK_mkeyL] at hr
    cases hfk : mvcc.findKey (mkeyL it.key') s.kvs with
    | none => rw [hfk] at hr; exact hr.elim
    | some v =>
      rw [hfk] at hr
      cases hd : driverCodec.dec v.value with
      | none => simp [hd] at hr; exact hr.elim
      | some oc =>
        simp only [Option.bind_some, hd, Option.map_some] at hr
        obtain ⟨ho, -⟩ := hr
        have hv : v ∈ s.kvs := List.mem_of_find?_eq_some hfk
        have hkey : v.key = mkeyL it.key' := findKey_key hfk
        refine ⟨v, hv, ?_, oc.1, oc.2, hd, ?_⟩
        · rw [hkey, mkeyL, prepareKeyM_scope _ _ _ hk]; exact hsc
        · rw [hkey, mkeyL, drop_registry, ho, hsn v hv]
  · rintro ⟨v, hv, hsc, d, c, hd, rfl⟩
    have hobj := prepareKeyM_objs _ _ _ hk hlk
    have hpre : go!"/registry/objs/" <+: v.key :=
      (List.prefix_append_right_inj go!"/registry").2 hobj |>.trans
        (kInScope_registry k v.key _ hsc)
    obtain ⟨n, hn⟩ := hpre
    have hkey : v.key = mkeyL n := by rw [← hn]; rfl
    have hfk : mvcc.findKey (mkeyL n) s.kvs = some v := by
      rw [← hkey]; exact txn.findKey_of_mem_sorted (KVStore.kvs_sorted s) hv
    have hr := hrel n
    rw [absK_mkeyL, hfk] at hr
    simp only [Option.bind_some, hd, Option.map_some] at hr
    rcases hlu : lookupL g.items n with ⟨it, b⟩
    rw [hlu] at hr
    cases b with
    | false => exact hr.elim
    | true =>
      obtain ⟨hit, hik⟩ := lookupL_some g.items n it true hlu rfl
      obtain ⟨ho, -⟩ := hr
      refine ⟨it, hit, ?_, ?_⟩
      · rw [hik, ← prepareKeyM_scope _ _ _ hk, ← mkeyL, ← hkey]; exact hsc
      · rw [hik, ho, hkey, mkeyL, drop_registry, hsn v hv]

/-! ## The answer -/

theorem mem_storeScope_key (kp : GoString) (r : Bool) (s : KVStore) (ko : GoString × (DObj × Nat))
    (h : ko ∈ storeScope kp r s) : kInScope kp r ko.1 = true := by
  unfold storeScope at h
  simp only [List.mem_filterMap, List.mem_filter, Option.map_eq_some_iff] at h
  obtain ⟨v, ⟨-, hsc⟩, _, -, rfl⟩ := h
  exact hsc

theorem storeScope_keys_sorted (kp : GoString) (r : Bool) (s : KVStore) :
    ((storeScope kp r s).map Prod.fst).Pairwise go.GoStringLt := by
  have hs := KVStore.kvs_sorted s
  unfold storeScope
  rw [List.pairwise_map, List.pairwise_filterMap]
  refine List.Pairwise.imp_of_mem ?_ (hs.filter (fun v => kInScope kp r v.key))
  intro a b _ _ hab ea hea eb heb
  simp only [Option.map_eq_some_iff] at hea heb
  obtain ⟨_, -, rfl⟩ := hea
  obtain ⟨_, -, rfl⟩ := heb
  exact hab

/-- Not recursive, the scope has at most one key. -/
theorem storeScope_short (kp : GoString) (s : KVStore) : (storeScope kp false s).length ≤ 1 := by
  have hs := storeScope_keys_sorted kp false s
  have hk : ∀ ko ∈ storeScope kp false s, ko.1 = kp := fun ko h => by
    have := mem_storeScope_key kp false s ko h
    unfold kInScope at this; simpa using this
  match hl : storeScope kp false s, hs, hk with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: _, hs, hk =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_cons, List.mem_map] at hs
    have := hs.1 b.1 (Or.inl rfl)
    rw [hk a (by simp), hk b (by simp)] at this
    exact absurd this (go.goStringLt_irrefl _)

/-- **The driver's list answer is the store's** (under `KRelS`). -/
theorem listOut_core (x : Input) (k : GoString) (g : GSt) (s : KVStore) (rv : Nat)
    (hS : KRelS s rv g) (hmod : ∀ v ∈ s.kvs, uint.Z v.modRev < 2 ^ 63)
    (hk : prepareKeyM go!"/objs" x.ListKey' x.Recursive' = some k)
    (hlk : go!"/objs/" <+: x.ListKey') :
    listOutL x g (listLoopL x g.items) k =
      listOutDriver x g.rv
        (kListL driverCodec.dec (selD x) (limN x.Limit') (go!"/registry" ++ k) x.Recursive' s) := by
  have hsc := scopeL_eq x k g s rv hS hmod hk hlk
  have hlim : limitN x = limN x.Limit' := rfl
  have hsel : (fun o : DObj × Nat => selOkL x (o.1.toObj (W64 (o.2 : Int)))) =
      (fun o => selD x o.1) := rfl
  have hkl : kListL driverCodec.dec (selD x) (limN x.Limit') (go!"/registry" ++ k) x.Recursive' s =
      ListModel.loop (fun o => selD x o.1) (limN x.Limit')
        (storeScope (go!"/registry" ++ k) x.Recursive' s) := rfl
  have hl : ListModel.loop (selOkL x) (limitN x)
      ((storeScope (go!"/registry" ++ k) x.Recursive' s).map toDrv) =
      ⟨(ListModel.loop (fun o : DObj × Nat => selOkL x (o.1.toObj (W64 (o.2 : Int)))) (limitN x)
          (storeScope (go!"/registry" ++ k) x.Recursive' s)).items.map
          (fun o : DObj × Nat => o.1.toObj (W64 (o.2 : Int))),
        (ListModel.loop (fun o : DObj × Nat => selOkL x (o.1.toObj (W64 (o.2 : Int)))) (limitN x)
          (storeScope (go!"/registry" ++ k) x.Recursive' s)).last.map (fun l : GoString => l.drop 9),
        (ListModel.loop (fun o : DObj × Nat => selOkL x (o.1.toObj (W64 (o.2 : Int)))) (limitN x)
          (storeScope (go!"/registry" ++ k) x.Recursive' s)).more,
        (ListModel.loop (fun o : DObj × Nat => selOkL x (o.1.toObj (W64 (o.2 : Int)))) (limitN x)
          (storeScope (go!"/registry" ++ k) x.Recursive' s)).total⟩ :=
    ListModel.loop_map (fun l : GoString => l.drop 9) (fun o : DObj × Nat => o.1.toObj (W64 (o.2 : Int)))
      (selOkL x) (limitN x) _
  unfold listLoopL
  rw [hsc, hl, hsel, hlim, hkl]
  generalize hA : ListModel.loop (fun o => selD x o.1) (limN x.Limit')
    (storeScope (go!"/registry" ++ k) x.Recursive' s) = A
  have hkp : (prepareKeyM go!"/objs" x.ListKey' x.Recursive').getD [] = k := by rw [hk]; rfl
  unfold listOutL listOutDriver
  simp only [hkp, List.map_reverse]
  cases hm : A.more
  · rfl
  · -- more: recursive, the last key in scope
    have hrec : x.Recursive' = true := by
      cases hr : x.Recursive'
      · rw [hr] at hA
        have := ListModel.loop_more_short (fun o => selD x o.1) (limN x.Limit') _
          (storeScope_short (go!"/registry" ++ k) s)
        rw [hA, hm] at this; cases this
      · rfl
    obtain ⟨l, hl⟩ := ListModel.loop_more_last _ _ _ (hA ▸ hm)
    rw [hA] at hl
    obtain ⟨ko, hko, hkol⟩ := ListModel.loop_last _ _ _ l (hA ▸ hl)
    have hin := mem_storeScope_key _ _ _ ko hko
    rw [hrec, hkol] at hin
    have hpre := kInScope_registry k l true hin
    obtain ⟨t, ht⟩ := (List.prefix_append go!"/registry" k).trans hpre
    have hok : encOkL (go!"/registry" ++ t ++ [W8 0]) (go!"/registry" ++ k) = true := by
      unfold encOkL
      rw [ht]
      simp only [decide_eq_true_eq]
      exact ⟨by simp, hpre.trans (List.prefix_append _ _)⟩
    simp only [hl, Option.map_some, Option.getD_some, ← ht, drop_registry, hok, ite_true]

/-- `pastReadL` is a read at a revision other than the latest (`listRevL`), for the driver's
matches. -/
theorem pastReadL_listRevL (x : Input) (n : w64)
    (hm : x.Match' = W64 0 ∨ x.Match' = W64 1 ∨ x.Match' = W64 2)
    (hn : parseRVD x.MinRV' = some n) :
    pastReadL x n = decide (uint.Z (listRevL (matchOptL x) x.Recursive' x.Limit' n) ≠ 0) := by
  have hz : x.MinRV' = [] → n = W64 0 := by
    intro h; rw [h] at hn; simp [parseRVD] at hn; exact hn.symm
  have hn0 : uint.Z n = 0 ↔ n = W64 0 := by
    constructor
    · intro h; apply BitVec.eq_of_toNat_eq; simp only [uint.Z] at h; simp; omega
    · intro h; subst h; rfl
  unfold pastReadL listRevL matchOptL
  rcases hm with h | h | h <;> rw [h]
  · by_cases h0 : n = W64 0
    · simp [h0]
    · have hmin : ¬ x.MinRV' = [] := fun e => h0 (hz e)
      have hnz : BitVec.toNat n ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simp [e]))
      have h0' : n ≠ 0#64 := h0
      have hpos : 0 < BitVec.toNat n := Nat.pos_of_ne_zero hnz
      have : 0 < uint.Z n := by simp only [uint.Z]; omega
      by_cases hr : x.Recursive' = true <;> by_cases hl : 0 < sint.Z x.Limit' <;>
        simp [hmin, h0', hpos, hr, hl, hnz]
  · by_cases h0 : n = W64 0 <;> simp [h0]
  · by_cases h0 : n = W64 0
    · simp [h0]
    · have hmin : ¬ x.MinRV' = [] := fun e => h0 (hz e)
      have hnz : BitVec.toNat n ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (by simp [e]))
      have h0' : n ≠ 0#64 := h0
      have hpos : 0 < BitVec.toNat n := Nat.pos_of_ne_zero hnz
      simp [hmin, h0', hnz]

/-- **`refine_list`** (`notes/k8s-7e-2-draft.md` §8 with corrections R1-R4): on related states,
the driver's list answers `ETooLarge` exactly when the store's is too large, and otherwise what the
driver's `listOut` makes of the store's `listIs` answer over `kListL` at the revision read. -/
theorem refine_list (x : Input) (h : HSt) (σ : KVState) (k : GoString) (n : w64)
    (hrel : KRelH h σ)
    (hm : x.Match' = W64 0 ∨ x.Match' = W64 1 ∨ x.Match' = W64 2)
    (hlk : go!"/objs/" <+: x.ListKey')
    (hk : prepareKeyM go!"/objs" x.ListKey' x.Recursive' = some k)
    (hn : parseRVD x.MinRV' = some n) :
    let R := listRevL (matchOptL x) x.Recursive' x.Limit' n
    let s := if uint.Z R = 0 then σ.store else σ.at (uint.nat R)
    let a := kListL driverCodec.dec (selD x) (limN x.Limit') (go!"/registry" ++ k) x.Recursive' s
    (if σ.rev < uint.nat n then tooLargeL = mlistL x h
     else listOutDriver x (if uint.Z R = 0 then W64 (σ.rev : Int) else R) a = mlistL x h) := by
  intro R s a
  obtain ⟨hlt, hcur, hhist, hmods⟩ := hrel
  have hrv : uint.nat h.st.rv = σ.rev := by
    rw [← hcur.2.1]; simp only [uint.nat, W64]; rw [BitVec.toNat_ofInt]; omega
  unfold mlistL
  rw [hn]
  simp only
  rw [hrv]
  by_cases hc : σ.rev < uint.nat n
  · simp [hc]
  · simp only [hc, ite_false, hk]
    unfold listStL
    rw [pastReadL_listRevL x n hm hn]
    by_cases hR : uint.Z R = 0
    · have : ¬ (uint.Z (listRevL (matchOptL x) x.Recursive' x.Limit' n) ≠ 0) := fun e => e hR
      simp only [this, decide_false, Bool.false_eq_true, ite_false]
      simp only [s, a, hR, ite_true]
      rw [listOut_core x k h.st σ.store σ.rev hcur (hmods σ.rev (Nat.le_refl _)) hk hlk,
        ← hcur.2.1]
    · have hRn : R = n := by
        simp only [R, listRevL] at hR ⊢
        by_cases h1 : matchOptL x = go!"Exact"
        · rw [if_pos h1]
        · by_cases h2 : matchOptL x = [] ∧ x.Recursive' = true ∧ 0 < sint.Z x.Limit' ∧ 0 < uint.Z n
          · rw [if_neg h1, if_pos h2]
          · rw [if_neg h1, if_neg h2] at hR; exact absurd rfl hR
      have hR' : uint.Z (listRevL (matchOptL x) x.Recursive' x.Limit' n) ≠ 0 := hR
      simp only [hR', ne_eq, not_false_eq_true, decide_true, ite_true]
      simp only [s, a, hR, ite_false]
      rw [hRn]
      have hn1 : 1 ≤ uint.nat n := by
        have : uint.Z n ≠ 0 := hRn ▸ hR
        simp only [uint.Z, uint.nat] at this ⊢; omega
      have hnn : W64 ((uint.nat n : Nat) : Int) = n := by
        apply BitVec.eq_of_toNat_eq; simp [uint.nat, W64]
      have hS := hhist (uint.nat n) hn1 (by omega)
      rw [hnn] at hS
      rw [listOut_core x k (histAtL h.hist n) (σ.at (uint.nat n)) (uint.nat n) hS
        (hmods (uint.nat n) (by omega)) hk hlk, ← hS.2.1, hnn]

end go

end k8s_etcd3
end EtcdGrove
end Perennial
