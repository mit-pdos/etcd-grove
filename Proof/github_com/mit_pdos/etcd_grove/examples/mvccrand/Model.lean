/-
The tester's model against mvcc's (pure; `notes/mvcc-migration/mvccrand.md`). Lean-first (no Rocq
counterpart).

The tester keeps each revision's state as a Go map from key to `kvRec` (`states[r]`); mvcc's API
states its reads over the history's state `stateAt L r` (a key-sorted list of `EtcdKv`).
`stMatch M s` says the map is the state. The probe of the read contract: **the keys a range read
answers (`rangeAnswers`, through which `Txn.Range.contract`'s `rangeOutcomeC` gives the count and
the key-values) are exactly the keys `checkRange` computes** (`matchKeys`: the tester's keys, in its
order, present in its map and in the range), for a well-formed log (`LogOk`, which the contract's
`LogWf'` and change-count facts give: `txn.LogOk.of_cert`). So `checkRange`'s count, its number of
key-values and their order are justified by the API; each key-value's fields by `rangeKvs`'s
`findKey` in the same state (`stMatch`'s first part).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.inRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.checkKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc

/-! ## Strictly sorted lists -/

/-- Two lists strictly sorted by an irreflexive, asymmetric relation, with the same members, are
equal. -/
theorem pairwise_ext {α : Type} {r : α → α → Prop} (irr : ∀ a, ¬ r a a)
    (asymm : ∀ a b, r a b → ¬ r b a) :
    ∀ {l₁ l₂ : List α}, l₁.Pairwise r → l₂.Pairwise r → (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      have ha := (h a).1 List.mem_cons_self
      have hb := (h b).2 List.mem_cons_self
      rcases List.mem_cons.1 ha with ha | ha
      · exact ha
      rcases List.mem_cons.1 hb with hb | hb
      · exact hb.symm
      exact absurd (h₂.1 a ha) (asymm _ _ (h₁.1 b hb))
    subst hab
    congr 1
    refine pairwise_ext irr asymm h₁.2 h₂.2 fun x => ?_
    constructor
    · intro hx
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd (h₁.1 x hx) (irr x)
      · exact e
    · intro hx
      rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · subst e; exact absurd (h₂.1 x hx) (irr x)
      · exact e

/-- The tester's keys are strictly increasing. -/
theorem keyList_sorted : keyList.Pairwise go.GoStringLt := by
  unfold keyList; decide

/-! ## The tester's states and the store's -/

section model
variable [GooseExts]

/-- The store's key-value of the model's record of `k`. -/
def kvOfRec (k : GoString) (e : kvRec) : EtcdKv :=
  { key := k, createRev := e.create', modRev := e.mod', version := e.ver', value := e.val',
    lease := e.lease' }

/-- **The tester's map `M` is the store's state `s`**: each key's key-value is the record's, and
every key of the state is one of the tester's (it writes no other). -/
def stMatch (M : GMap GoString kvRec) (s : List EtcdKv) : Prop :=
  (∀ k, findKey k s = (M !! k).map (kvOfRec k)) ∧ ∀ v ∈ s, v.key ∈ keyList

/-- **The keys `checkRange` expects** (`match`): the tester's keys, in order, in its map and in the
range. -/
def matchKeys (M : GMap GoString kvRec) (endNil : Bool) (k e : GoString) : List GoString :=
  keyList.filter fun key => (M !! key).isSome && inRangeM endNil k e key

theorem srvInRange_eq (endNil : Bool) (k e key : GoString) :
    txn.srvInRange endNil k e key = inRangeM endNil k e key := by
  unfold txn.srvInRange inRangeM; rfl

theorem findKey_isSome_iff (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (x : GoString) :
    (findKey x s).isSome = true ↔ x ∈ s.map EtcdKv.key := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    unfold findKey at hv
    have hm := List.mem_of_find?_eq_some hv
    have hk := List.find?_some hv
    simp only [decide_eq_true_eq] at hk
    exact List.mem_map.2 ⟨v, hm, hk⟩
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
    rw [txn.findKey_of_mem_sorted hs hv]; rfl

/-- **The probe of the read contract**: the keys a range read of a well-formed log answers at
revision `r` are exactly the keys `checkRange` computes from the matching map. -/
theorem answers_keys_eq_match (L : Log) (hok : txn.LogOk L) (endNil : Bool) (k e : GoString)
    (r : Nat) (hr : r < 2 ^ 63) (M : GMap GoString kvRec) (hM : stMatch M (stateAt L r)) :
    (rangeAnswers L endNil k e (W64 r)).map Prod.fst = matchKeys M endNil k e := by
  rw [txn.rangeAnswers_keys L hok endNil k e r hr]
  have hs := stateAt_sorted L r
  unfold txn.srvSel matchKeys
  rw [show (fun v : EtcdKv => txn.srvInRange endNil k e v.key) =
      (txn.srvInRange endNil k e) ∘ EtcdKv.key from rfl, ← List.filter_map]
  have hks : (List.map EtcdKv.key (stateAt L r)).Pairwise go.GoStringLt :=
    List.pairwise_map.2 hs
  apply pairwise_ext go.goStringLt_irrefl (fun _ _ h => go.goStringLt_asymm h)
    (hks.filter _) (keyList_sorted.filter _)
  intro x
  simp only [List.mem_filter, srvInRange_eq, Bool.and_eq_true]
  have hx : (M !! x).isSome = true ↔ x ∈ (stateAt L r).map EtcdKv.key := by
    rw [← findKey_isSome_iff _ hs, hM.1 x]
    cases M !! x <;> simp
  constructor
  · rintro ⟨hm, hin⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hm
    exact ⟨hM.2 v hv, hx.2 hm, hin⟩
  · rintro ⟨-, hm, hin⟩
    exact ⟨hx.1 hm, hin⟩

/-- **The probe of the watch range** (`WatchStream.Watch.contract` registers `watchRangeOf kk e
endk startRev id`, whose `covers` selects a watcher's events in `wsRecvOk`): for non-empty keys it
is the tester's `inRange` (the affine order's empty end, `[]byte{}`, is the from-key range). -/
theorem covers_eq_inRangeM (kk e : GoString) (endk : GoSlice) (s id : w64) (k : GoString)
    (hk : k ≠ []) (hkk : kk ≠ []) :
    (watchRangeOf kk e endk s id).covers k = inRangeM (decide (endk = slice.nil)) kk e k := by
  unfold watchRangeOf WatchRange.covers inRangeM
  by_cases hn : endk = slice.nil
  · simp [hn]
  · simp only [hn, ↓reduceIte, decide_false, Bool.false_eq_true, mvcc.inRange]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Bool.or_eq_true]
    rw [adt.affCmp_nonneg_iff, adt.affCmp_neg_iff, adt.affLt_iff_of_ne k kk hkk]
    unfold adt.affLt
    have hk' : k ≠ go!"" := hk
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨fun h => h1 ⟨hk', h⟩, h2.elim (fun h => Or.inl (by simpa using h)) Or.inr⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 h.2, hk', h2.elim (fun h => Or.inl (by simpa using h)) Or.inr⟩

end model

end mvccrand
end EtcdGrove
end Perennial
