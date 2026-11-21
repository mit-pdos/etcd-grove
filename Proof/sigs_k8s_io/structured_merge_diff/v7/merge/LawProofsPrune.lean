/-
**`prune`'s passes keep the object conforming** (`prune_conforms`, `merge/Laws.lean`; D10 (b)):
the general fact (`Prune.removeAt_conforms`: removing a set `R` from a conforming value keeps it
conforming when `R` is key-closed (a list item's key field goes only with the item) and has no
path strictly below an atomic node reached through granular types), and each of `prune`'s three
removal sets has both.
Prove phase (2026-11-21).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsGlue

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace Prune

open Glue (mem_single not_mem_pempty mem_punion)

/-! ## The removal sets that keep a value conforming -/

/-- A list item's key field is removed only with the item. -/
def KeyClosed (R : PathSet) : Prop :=
  ∀ p fl n v, (n, v) ∈ fl → (p ++ [PE.key fl, .field n]) ∈ R → (p ++ [PE.key fl]) ∈ R

/-- No path strictly below a (non-root) atomic node reached through granular types. -/
def NoBelowAtomic (S : Schema) (t : TypeRef) (R : PathSet) : Prop :=
  ∀ p r t', p ≠ [] → r ≠ [] → (p ++ r) ∈ R → reconAt S t p = some t' → isAtomicT S t' = false

theorem mem_under {R : PathSet} {pe : PE} {q : Path} : q ∈ R.under pe ↔ q ≠ [] ∧ (pe :: q) ∈ R :=
  PathSet_mem_under_law_holds R pe q

theorem keyClosed_under {R : PathSet} (h : KeyClosed R) (pe : PE) : KeyClosed (R.under pe) := by
  intro p fl n v hn hm
  rw [mem_under] at hm ⊢
  refine ⟨by simp, ?_⟩
  have := h (pe :: p) fl n v hn (by simpa using hm.2)
  simpa using this

theorem nba_under {S : Schema} {t : TypeRef} {R : PathSet} (h : NoBelowAtomic S t R) (pe : PE)
    (t'' : TypeRef) (hg : isGranularT S t = true) (hc : reconChild S t pe = some t'') :
    NoBelowAtomic S t'' (R.under pe) := by
  intro p r t' hp hr hm ha
  rw [mem_under] at hm
  exact h (pe :: p) r t' (by simp) hr (by simpa using hm.2) (by simp [reconAt, hg, hc, ha])

/-! ## Conformance facts -/

theorem find_isSome_of_conforms {S : Schema} {t : TypeRef} {x : UVal} (h : conforms S t x) :
    (S.find t.name).isSome := by
  unfold conforms at h
  cases hf : S.find t.name with
  | some _ => rfl
  | none => cases x <;> simp [conformsB, hf] at h

theorem conforms_null {S : Schema} {t : TypeRef} (h : (S.find t.name).isSome) :
    conforms S t .null := by
  unfold conforms
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h
  cases a <;> simp [conformsB, ha, scalarOk]

/-! ## A list item keeps its key -/

theorem lookupKV_removeM_none (S : Schema) (fs : List (GoString × TypeRef)) (em : Option TypeRef)
    (R : PathSet) (k : GoString) :
    ∀ kvs, lookupKV k kvs = none → lookupKV k (removeM S fs em R kvs) = none
  | [], _ => by simp [removeM, lookupKV]
  | (k', v) :: kvs, h => by
    unfold lookupKV at h
    split at h
    · cases h
    rename_i hne
    have ih := lookupKV_removeM_none S fs em R k kvs h
    simp only [removeM]
    split
    · exact ih
    · split <;> simp [lookupKV, hne, ih]

theorem lookupKV_removeM_scalar (S : Schema) (fs : List (GoString × TypeRef))
    (em : Option TypeRef) (R : PathSet) (k : GoString) (kt : TypeRef) (sc : Scalar)
    (hft : fieldType fs em k = some kt) (hsc : S.find kt.name = some (.scalar sc))
    (hk : [PE.field k] ∉ R) :
    ∀ kvs, lookupKV k (removeM S fs em R kvs) = lookupKV k kvs
  | [] => by simp [removeM]
  | (k', v) :: kvs => by
    have ih := lookupKV_removeM_scalar S fs em R k kt sc hft hsc hk kvs
    simp only [removeM]
    split
    · next hin =>
      have hne : k' ≠ k := by rintro rfl; exact hk hin
      simp [lookupKV, hne, ih]
    · split
      · by_cases hkk : k' = k
        · subst hkk
          simp only [lookupKV, ite_true, hft]
          rw [removeAt_scalar_law_holds S kt sc _ v hsc]
        · simp [lookupKV, hkk, ih]
      · by_cases hkk : k' = k
        · subst hkk; simp [lookupKV]
        · simp [lookupKV, hkk, ih]

theorem keyOf_congr (ks : List GoString) (kvs kvs' : List (GoString × UVal))
    (h : ∀ k ∈ ks, lookupKV k kvs' = lookupKV k kvs) : keyOf ks (.map kvs') = keyOf ks (.map kvs) := by
  have : ks.filterMap (fun k => (lookupKV k kvs').map (fun v => (k, v))) =
      ks.filterMap (fun k => (lookupKV k kvs).map (fun v => (k, v))) := by
    induction ks with
    | nil => rfl
    | cons k ks ih =>
      simp only [List.filterMap_cons, h k List.mem_cons_self,
        ih (fun k hk => h k (List.mem_cons_of_mem _ hk))]
  simp only [keyOf, this]

/-- An item of an associative list with paths of `R` below it (not itself) keeps its key. -/
theorem item_key (S : Schema) (hS : S.WF) (t e : TypeRef) (ks : List GoString) (R : PathSet)
    (v : UVal) (pe : PE) (hf : S.find t.name = some (.list e .associative ks))
    (hk : keyOf ks v = some pe) (hpe : [pe] ∉ R) (hkc : KeyClosed R)
    (hnb : NoBelowAtomic S t R) (hne : ¬ (R.under pe).IsEmpty) :
    keyOf ks (removeAt S e (R.under pe) v) = some pe := by
  obtain ⟨kvs, rfl⟩ := LawB.keyOf_map ks v _ hk
  obtain ⟨-, -, fs, em, rel', hfe, hkf⟩ := LawB.list_wf S hS t e .associative ks hf (by simp)
  -- a path below the item
  obtain ⟨r, hr⟩ : ∃ r, r ∈ R.under pe := by
    unfold PathSet.IsEmpty at hne
    rw [FSet_isEmpty_iff_law_holds] at hne
    simpa using hne
  have hr' := mem_under.1 hr
  have hgr : isGranularT S t = true := by simp [isGranularT, hf]
  have hrel : rel' ≠ .atomic := by
    rintro rfl
    have := hnb [pe] r e (by simp) hr'.1 (by simpa using hr'.2)
      (by simp [reconAt, hgr, reconChild, hf])
    simp [isAtomicT, hfe] at this
  -- the key's fields
  have hkey : ∀ k ∈ ks, lookupKV k (removeM S fs em (R.under pe) kvs) = lookupKV k kvs := by
    intro k hks
    cases hl : lookupKV k kvs with
    | none => exact lookupKV_removeM_none S fs em _ k kvs hl
    | some w =>
      have hkn := hkf k hks
      unfold keyFieldOk at hkn
      split at hkn
      · next kt hkt =>
        split at hkn
        · next sc hsc =>
          have hft : fieldType fs em k = some kt := by simp [fieldType, hkt]
          rw [← hl]
          refine lookupKV_removeM_scalar S fs em _ k kt sc hft hsc ?_ kvs
          intro hin
          apply hpe
          have hin' := (mem_under.1 hin).2
          simp only [keyOf] at hk
          split at hk
          · cases hk
          · simp only [Option.some.injEq] at hk
            subst hk
            have hmem : (k, w) ∈ flSort (ks.filterMap (fun k => (lookupKV k kvs).map (fun v => (k, v)))) :=
              (LawB.flSort_perm _).mem_iff.2 ((LawB.mem_keyFields ks kvs k w).2 ⟨hks, hl⟩)
            have := hkc [] _ k w hmem (by simpa using hin')
            simpa using this
        · simp at hkn
      · simp at hkn
  -- the item's map stays non-empty
  have hne' : removeM S fs em (R.under pe) kvs ≠ [] := by
    intro h0
    simp only [keyOf] at hk
    split at hk
    · cases hk
    · next hfl =>
      obtain ⟨⟨k, w⟩, hkw⟩ := List.exists_mem_of_ne_nil _ hfl
      obtain ⟨hks, hlk⟩ := (LawB.mem_keyFields ks kvs k w).1 hkw
      have := hkey k hks
      rw [h0, hlk] at this
      simp [lookupKV] at this
  have hkvs : kvs ≠ [] := by
    rintro rfl; simp [removeM] at hne'
  have hrm : removeAt S e (R.under pe) (.map kvs) = .map (removeM S fs em (R.under pe) kvs) := by
    simp only [removeAt, hfe]
    rw [ite_eq_right (by simp [hkvs, hrel])]
  rw [hrm, keyOf_congr ks kvs _ hkey, hk]

/-! ## Removing a key-closed set below no atomic node keeps a value conforming -/

theorem keysOf_cons_some {ks : List GoString} {v : UVal} {pe : PE} (vs : List UVal)
    (h : keyOf ks v = some pe) : keysOf ks (v :: vs) = pe :: keysOf ks vs := by
  simp [keysOf, h]

mutual
theorem rm_at (S : Schema) (hS : S.WF) : ∀ (x : UVal) (t : TypeRef) (R : PathSet),
    conforms S t x → KeyClosed R → NoBelowAtomic S t R → conforms S t (removeAt S t R x)
  | .list vs, t, R, hc, hk, hn => by
    have hsome := find_isSome_of_conforms hc
    cases hf : S.find t.name with
    | none => simp [hf] at hsome
    | some a =>
      cases a with
      | scalar sc => simpa [removeAt, hf] using hc
      | map fs em rel => simpa [removeAt, hf] using conforms_null hsome
      | list e rel ks =>
        by_cases hemp : vs.isEmpty = true ∨ rel = .atomic
        · simp only [removeAt, hf, if_pos hemp]; exact conforms_null hsome
        · simp only [removeAt, hf, if_neg hemp]
          have hrel : rel ≠ .atomic := fun h => hemp (Or.inr h)
          obtain ⟨hassoc, -, -⟩ := LawB.list_wf S hS t e rel ks hf hrel
          subst hassoc
          obtain ⟨hcs, hkeys⟩ := conforms_item_law_holds S t e .associative ks vs hf hc
          obtain ⟨hok, hnd⟩ := hkeys rfl
          obtain ⟨h1, h2⟩ := rm_L S hS vs t e ks R hf hk hn hcs hok
          rcases hout : removeL S e ks R vs with _ | ⟨a, l⟩
          · exact conforms_null hsome
          · rw [hout] at h1 h2
            unfold conforms
            simp only [conformsB, hf, Bool.and_eq_true, ite_true, List.all_eq_true,
              decide_eq_true_eq]
            refine ⟨(LawA.conformsL_iff S e _).2 (fun v hv => (h1 v hv).1),
              fun v hv => (h1 v hv).2, h2.nodup hnd⟩
  | .map kvs, t, R, hc, hk, hn => by
    have hsome := find_isSome_of_conforms hc
    cases hf : S.find t.name with
    | none => simp [hf] at hsome
    | some a =>
      cases a with
      | scalar sc => simpa [removeAt, hf] using hc
      | list e rel ks => simpa [removeAt, hf] using conforms_null hsome
      | map fs em rel =>
        by_cases hemp : kvs.isEmpty = true ∨ rel = .atomic
        · simp only [removeAt, hf, if_pos hemp]; exact conforms_null hsome
        · simp only [removeAt, hf, if_neg hemp]
          have hrel : rel ≠ .atomic := fun h => hemp (Or.inr h)
          have he := conforms_entry_law_holds S t fs em rel kvs hf hc
          have hm := rm_M S hS kvs t fs em rel R hf hrel hk hn he
          rcases hout : removeM S fs em R kvs with _ | ⟨a, l⟩
          · exact conforms_null hsome
          · rw [hout] at hm
            unfold conforms
            simpa [conformsB, hf] using hm
  | .null, t, R, hc, _, _ => by
    have hsome := find_isSome_of_conforms hc
    unfold removeAt; split
    · exact hc
    · exact conforms_null hsome
  | .bool _, t, R, hc, _, _ => by
    have hsome := find_isSome_of_conforms hc
    unfold removeAt; split
    · exact hc
    · exact conforms_null hsome
  | .int _, t, R, hc, _, _ => by
    have hsome := find_isSome_of_conforms hc
    unfold removeAt; split
    · exact hc
    · exact conforms_null hsome
  | .str _, t, R, hc, _, _ => by
    have hsome := find_isSome_of_conforms hc
    unfold removeAt; split
    · exact hc
    · exact conforms_null hsome
theorem rm_L (S : Schema) (hS : S.WF) : ∀ (vs : List UVal) (t e : TypeRef) (ks : List GoString)
    (R : PathSet), S.find t.name = some (.list e .associative ks) → KeyClosed R →
    NoBelowAtomic S t R → (∀ v ∈ vs, conforms S e v) → (∀ v ∈ vs, itemKeyOk ks v) →
    (∀ v ∈ removeL S e ks R vs, conforms S e v ∧ itemKeyOk ks v) ∧
      (keysOf ks (removeL S e ks R vs)).Sublist (keysOf ks vs)
  | [], _, _, _, _, _, _, _, _, _ => by simp [removeL, keysOf]
  | v :: vs, t, e, ks, R, hf, hk, hn, hcs, hok => by
    have ih := rm_L S hS vs t e ks R hf hk hn (fun w hw => hcs w (List.mem_cons_of_mem _ hw))
      (fun w hw => hok w (List.mem_cons_of_mem _ hw))
    have hcv := hcs v List.mem_cons_self
    have hov := hok v List.mem_cons_self
    cases hkv : keyOf ks v with
    | none => simp [itemKeyOk, hkv] at hov
    | some pe =>
      rw [keysOf_cons_some vs hkv]
      simp only [removeL, hkv]
      split
      · exact ⟨ih.1, ih.2.cons pe⟩
      · next hpe =>
        split
        · next hne =>
          have hgr : isGranularT S t = true := by simp [isGranularT, hf]
          have hc' := rm_at S hS v e (R.under pe) hcv (keyClosed_under hk pe)
            (nba_under hn pe e hgr (by simp [reconChild, hf]))
          have hk' := item_key S hS t e ks R v pe hf hkv hpe hk hn hne
          refine ⟨?_, ?_⟩
          · intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact ⟨hc', by simp [itemKeyOk, hk']⟩
            · exact ih.1 w hw
          · rw [keysOf_cons_some _ hk']; exact ih.2.cons_cons pe
        · refine ⟨?_, ?_⟩
          · intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact ⟨hcv, hov⟩
            · exact ih.1 w hw
          · rw [keysOf_cons_some _ hkv]; exact ih.2.cons_cons pe
theorem rm_M (S : Schema) (hS : S.WF) : ∀ (kvs : List (GoString × UVal)) (t : TypeRef)
    (fs : List (GoString × TypeRef)) (em : Option TypeRef) (rel : ElemRel) (R : PathSet),
    S.find t.name = some (.map fs em rel) → rel ≠ .atomic → KeyClosed R → NoBelowAtomic S t R →
    (∀ k v, (k, v) ∈ kvs → ∃ t', fieldType fs em k = some t' ∧ conforms S t' v) →
    conformsM S fs em (removeM S fs em R kvs) = true
  | [], _, _, _, _, _, _, _, _, _, _ => by simp [removeM, conformsM]
  | (k, v) :: kvs, t, fs, em, rel, R, hf, hrel, hk, hn, he => by
    have ih := rm_M S hS kvs t fs em rel R hf hrel hk hn
      (fun k' v' h => he k' v' (List.mem_cons_of_mem _ h))
    obtain ⟨t', ht', hcv⟩ := he k v List.mem_cons_self
    simp only [removeM]
    split
    · exact ih
    · split
      · have hgr : isGranularT S t = true := by simp [isGranularT, hf, hrel]
        have hc' := rm_at S hS v t' (R.under (.field k)) hcv (keyClosed_under hk _)
          (nba_under hn _ t' hgr (by simp [reconChild, hf, ht']))
        simp only [conformsM, ht', Bool.and_eq_true]
        exact ⟨hc', ih⟩
      · simp only [conformsM, ht', Bool.and_eq_true]
        exact ⟨hcv, ih⟩
end

/-- **Removing a key-closed set with nothing below an atomic node keeps a value conforming.** -/
theorem removeItems_conforms (S : Schema) (hS : S.WF) (t : TypeRef) (x : UVal) (R : PathSet)
    (hc : conforms S t x) (hk : KeyClosed R) (hn : NoBelowAtomic S t R) :
    conforms S t (removeItems S t x R) :=
  rm_at S hS x t R hc hk hn

/-! ## Field sets descend only through granular types -/

/-- Every node strictly above the end of `q` (relative to `t`) is reached through granular
types (the reconciling walker's and `ensureNamed`'s descents agree there), a list's for a key, a
map's for a field. -/
def GranAt (S : Schema) (t : TypeRef) (q : Path) : Prop :=
  ∀ p pe r, q = p ++ pe :: r → ∃ tp, reconAt S t p = some tp ∧ typeAlong S (some t) p = some tp ∧
    isGranularT S tp = true ∧
    (∀ fl, pe = .key fl → ∃ e rel ks, S.find tp.name = some (.list e rel ks)) ∧
    (∀ n, pe = .field n → ∃ fs em rel, S.find tp.name = some (.map fs em rel))

theorem granAt_nil (S : Schema) (t : TypeRef) : GranAt S t [] := by
  intro p pe r h; simp at h

theorem granAt_cons (S : Schema) (t t' : TypeRef) (pe : PE) (q : Path)
    (hg : isGranularT S t = true) (hc : reconChild S t pe = some t')
    (hcT : childType S (some t) pe = some t')
    (hk : ∀ fl, pe = .key fl → ∃ e rel ks, S.find t.name = some (.list e rel ks))
    (hf : ∀ n, pe = .field n → ∃ fs em rel, S.find t.name = some (.map fs em rel))
    (h : GranAt S t' q) : GranAt S t (pe :: q) := by
  intro p pe' r hq
  cases p with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hq
    obtain ⟨rfl, -⟩ := hq
    exact ⟨t, rfl, rfl, hg, hk, hf⟩
  | cons a p =>
    simp only [List.cons_append, List.cons.injEq] at hq
    obtain ⟨rfl, hq⟩ := hq
    obtain ⟨tp, h1, h2, h3, h4, h5⟩ := h p pe' r hq
    refine ⟨tp, ?_, ?_, h3, h4, h5⟩
    · simp [reconAt, hg, hc, h1]
    · simp [typeAlong, hcT, h2]

theorem keyOf_key {ks : List GoString} {v : UVal} {pe : PE} (h : keyOf ks v = some pe) :
    ∃ fl, pe = .key fl := by
  cases v <;> simp only [keyOf, reduceCtorEq] at h
  split at h
  · cases h
  · cases h; exact ⟨_, rfl⟩

mutual
theorem gran_at (S : Schema) : ∀ (x : UVal) (t : TypeRef) (P q : Path),
    q ∈ fieldsAt S t P x → ∃ q', q = P ++ q' ∧ GranAt S t q'
  | .list vs, t, P, q, hq => by
    rw [fieldsAt] at hq
    split at hq
    · exact ⟨[], by simpa using (mem_single.1 hq).1, granAt_nil S t⟩
    · next e rel ks hne hf => exact gran_L S vs t e rel ks P hf hne q hq
    · exact absurd hq not_mem_pempty
  | .map kvs, t, P, q, hq => by
    rw [fieldsAt] at hq
    split at hq
    · exact ⟨[], by simpa using (mem_single.1 hq).1, granAt_nil S t⟩
    · next fs em rel hne hf => exact gran_M S kvs t fs em rel P hf hne q hq
    · exact absurd hq not_mem_pempty
  | .null, t, P, q, hq => by
    unfold fieldsAt at hq
    split at hq <;> first
      | exact absurd hq not_mem_pempty
      | exact ⟨[], by simpa using (mem_single.1 hq).1, granAt_nil S t⟩
  | .bool _, t, P, q, hq => by
    unfold fieldsAt at hq
    split at hq <;> first
      | exact absurd hq not_mem_pempty
      | exact ⟨[], by simpa using (mem_single.1 hq).1, granAt_nil S t⟩
  | .int _, t, P, q, hq => by
    unfold fieldsAt at hq
    split at hq <;> first
      | exact absurd hq not_mem_pempty
      | exact ⟨[], by simpa using (mem_single.1 hq).1, granAt_nil S t⟩
  | .str _, t, P, q, hq => by
    unfold fieldsAt at hq
    split at hq <;> first
      | exact absurd hq not_mem_pempty
      | exact ⟨[], by simpa using (mem_single.1 hq).1, granAt_nil S t⟩
theorem gran_L (S : Schema) : ∀ (vs : List UVal) (t e : TypeRef) (rel : ElemRel)
    (ks : List GoString) (P : Path), S.find t.name = some (.list e rel ks) → rel ≠ .atomic →
    ∀ q, q ∈ fieldsL S e ks P vs → ∃ q', q = P ++ q' ∧ GranAt S t q'
  | [], _, _, _, _, _, _, _, q, hq => by rw [fieldsL] at hq; exact absurd hq not_mem_pempty
  | v :: vs, t, e, rel, ks, P, hf, hne, q, hq => by
    cases hk : keyOf ks v with
    | none =>
      simp only [fieldsL, hk] at hq
      exact gran_L S vs t e rel ks P hf hne q hq
    | some pe =>
      simp only [fieldsL, hk] at hq
      obtain ⟨fl, rfl⟩ := keyOf_key hk
      have hg : isGranularT S t = true := by simp [isGranularT, hf, hne]
      have hcons : ∀ q'', GranAt S e q'' → GranAt S t (.key fl :: q'') := fun q'' h =>
        granAt_cons S t e _ q'' hg (by simp [reconChild, hf]) (by simp [childType, hf])
          (fun _ _ => ⟨e, rel, ks, hf⟩) (fun _ h => by cases h) h
      rcases mem_punion.1 hq with hq | hq
      · rcases mem_punion.1 hq with hq | hq
        · obtain ⟨q'', rfl, h⟩ := gran_at S v e (P ++ [.key fl]) q hq
          exact ⟨.key fl :: q'', by simp, hcons q'' h⟩
        · exact ⟨[.key fl], by simpa using (mem_single.1 hq).1, hcons [] (granAt_nil S e)⟩
      · exact gran_L S vs t e rel ks P hf hne q hq
theorem gran_M (S : Schema) : ∀ (kvs : List (GoString × UVal)) (t : TypeRef)
    (fs : List (GoString × TypeRef)) (em : Option TypeRef) (rel : ElemRel) (P : Path),
    S.find t.name = some (.map fs em rel) → rel ≠ .atomic →
    ∀ q, q ∈ fieldsM S fs em P kvs → ∃ q', q = P ++ q' ∧ GranAt S t q'
  | [], _, _, _, _, _, _, _, q, hq => by rw [fieldsM] at hq; exact absurd hq not_mem_pempty
  | (k, u) :: kvs, t, fs, em, rel, P, hf, hne, q, hq => by
    rw [fieldsM] at hq
    rcases mem_punion.1 hq with hq | hq
    · split at hq
      · next tk htk =>
        have hg : isGranularT S t = true := by simp [isGranularT, hf, hne]
        have hcons : ∀ q'', GranAt S tk q'' → GranAt S t (.field k :: q'') := fun q'' h =>
          granAt_cons S t tk _ q'' hg (by simp [reconChild, hf, htk])
            (by simp [childType, hf, htk]) (fun _ h => by cases h)
            (fun _ _ => ⟨fs, em, rel, hf⟩) h
        rcases mem_punion.1 hq with hq | hq
        · obtain ⟨q'', rfl, h⟩ := gran_at S u tk (P ++ [.field k]) q hq
          exact ⟨.field k :: q'', by simp, hcons q'' h⟩
        · split at hq
          · exact ⟨[.field k], by simpa using (mem_single.1 hq).1, hcons [] (granAt_nil S tk)⟩
          · exact absurd hq not_mem_pempty
      · exact absurd hq not_mem_pempty
    · exact gran_M S kvs t fs em rel P hf hne q hq
end

theorem granular_not_atomic {S : Schema} {t : TypeRef} (h : isGranularT S t = true) :
    isAtomicT S t = false := by
  cases hf : S.find t.name with
  | none => simp [isGranularT, hf] at h
  | some a =>
    cases a with
    | scalar => simp [isGranularT, hf] at h
    | list e rel ks => cases rel <;> simp_all [isGranularT, isAtomicT]
    | map fs em rel => cases rel <;> simp_all [isGranularT, isAtomicT]

/-! ## Facts of the removal sets -/

theorem nba_mono {S : Schema} {t : TypeRef} {R R' : PathSet} (h : ∀ q, q ∈ R → q ∈ R')
    (h' : NoBelowAtomic S t R') : NoBelowAtomic S t R :=
  fun p r t' hp hr hm ha => h' p r t' hp hr (h _ hm) ha

theorem nba_fieldSet (S : Schema) (t : TypeRef) (x : UVal) :
    NoBelowAtomic S t (fieldSet S t x) := by
  intro p r t' hp hr hm ha
  obtain ⟨q', hq', hg⟩ := gran_at S x t [] _ hm
  simp only [List.nil_append] at hq'
  obtain ⟨pe, r', rfl⟩ := List.exists_cons_of_ne_nil hr
  obtain ⟨tp, h1, -, h3, -⟩ := hg p pe r' hq'.symm
  rw [ha] at h1; cases h1
  exact granular_not_atomic h3

theorem nba_of_consistent {S : Schema} {t : TypeRef} {s : PathSet} (h : schemaConsistent S t s) :
    NoBelowAtomic S t s := by
  intro p r t' hp hr hm ha
  unfold schemaConsistent at h
  rw [FSet_isEmpty_iff_law_holds] at h
  cases hat : isAtomicT S t' with
  | false => rfl
  | true => exact absurd ((atomicNodes_mem_law_holds S t s p).2 ⟨hp, ⟨r, hr, hm⟩, t', ha, hat⟩) (h p)

theorem ens_of_mem {S : Schema} {t : TypeRef} {s : PathSet} {q : Path} (h : q ∈ s) :
    q ∈ ensureNamed S t s :=
  (ensureNamed_mem_law_holds S t s q).2 (Or.inl h)

/-- `ensureNamed` adds only paths ending in a field. -/
theorem ens_key {S : Schema} {t : TypeRef} {s : PathSet} {p : Path} {fl : FieldList}
    (h : (p ++ [PE.key fl]) ∈ ensureNamed S t s) : (p ++ [PE.key fl]) ∈ s := by
  rcases (ensureNamed_mem_law_holds S t s _).1 h with h | ⟨p', n, he, -⟩
  · exact h
  · have := (List.append_inj' he rfl).2
    simp at this

/-- A key field's path of `ensureNamed s` is one of `s` (nothing is below it in `s`). -/
theorem ens_kf {S : Schema} {t : TypeRef} {s : PathSet} (hk : keysWithItems S t s) {p : Path}
    {fl : FieldList} {n : GoString} {v : UVal} (hn : (n, v) ∈ fl)
    (h : (p ++ [PE.key fl, .field n]) ∈ ensureNamed S t s) : (p ++ [PE.key fl, .field n]) ∈ s := by
  rcases (ensureNamed_mem_law_holds S t s _).1 h with h | ⟨p', n', -, ⟨r, hr, hm⟩, -⟩
  · exact h
  · exact absurd hm ((hk p fl).2.2 n v r hn hr)

theorem kc_ensureNamed {S : Schema} {t : TypeRef} {s : PathSet} (hk : keysWithItems S t s) :
    KeyClosed (ensureNamed S t s) := by
  intro p fl n v hn h
  exact ens_of_mem ((hk p fl).1 ⟨n, v, hn, ens_kf hk hn h⟩)

theorem nba_ensureNamed {S : Schema} {t : TypeRef} {s : PathSet} (h : NoBelowAtomic S t s) :
    NoBelowAtomic S t (ensureNamed S t s) := by
  intro p r t' hp hr hm ha
  rcases (ensureNamed_mem_law_holds S t s _).1 hm with hm | ⟨p', n, -, ⟨r', hr', hm'⟩, -⟩
  · exact h p r t' hp hr hm ha
  · exact h p (r ++ r') t' hp (by simp [hr]) (by simpa using hm') ha

theorem mem_pdiff {a b : PathSet} {q : Path} : q ∈ PathSet.diff a b ↔ q ∈ a ∧ q ∉ b := by
  unfold PathSet.diff; exact FSet_mem_diff_law_holds a b q

theorem mem_pinter {a b : PathSet} {q : Path} : q ∈ PathSet.inter a b ↔ q ∈ a ∧ q ∈ b := by
  unfold PathSet.inter; exact FSet_mem_inter_law_holds a b q

/-- A key field's path in `ensureNamed` of a conforming value's field set: in the field set, with
its item, whose type is a granular map. -/
theorem item_facts (S : Schema) (hS : S.WF) (t : TypeRef) (x : UVal) (hc : conforms S t x)
    {p : Path} {fl : FieldList} {n : GoString} {v : UVal} (hn : (n, v) ∈ fl)
    (h : (p ++ [PE.key fl, .field n]) ∈ ensureNamed S t (fieldSet S t x)) :
    (p ++ [PE.key fl, .field n]) ∈ fieldSet S t x ∧ (p ++ [PE.key fl]) ∈ fieldSet S t x ∧
    ∃ fs e rel, (typeAlong S (some t) (p ++ [.key fl])).bind (fun t => S.find t.name) =
      some (.map fs e rel) ∧ rel ≠ .atomic := by
  have K := Glue.kwi_fieldSet S t x hS hc
  have hkF := ens_kf K hn h
  refine ⟨hkF, (K p fl).1 ⟨n, v, hn, hkF⟩, ?_⟩
  obtain ⟨q', hq', hg⟩ := gran_at S x t [] _ hkF
  simp only [List.nil_append] at hq'
  obtain ⟨tp, -, h2, h3, -, h5⟩ := hg (p ++ [.key fl]) (.field n) [] (by rw [← hq']; simp)
  obtain ⟨fs, em, rel, hf⟩ := h5 n rfl
  refine ⟨fs, em, rel, by simp [h2, hf], ?_⟩
  rintro rfl
  simp [isGranularT, hf] at h3

/-- The managers' sets, each `keysWithItems` (sorted: every entry is its manager's). -/
theorem kwi_of_mem (S : Schema) (t : TypeRef) (mf : MF) (hs : keysSorted mf = true)
    (hk : ∀ m e, mf.get m = some e → keysWithItems S t e.set) :
    ∀ me ∈ mf, keysWithItems S t me.2.set := by
  intro me hme
  exact hk me.1 me.2 (fpD.mem_lookupKV mf me.1 me.2 (fpD.keysSorted_pairwise mf hs) hme)

/-! ## `prune_conforms`, restated -/

/-- **`prune`'s passes keep the object conforming**, with the two premises `prune_conforms`
lacks: the last set has nothing below an atomic node (`schemaConsistent`; without it a path
below an item of an atomic map type nulls the item) and the managers are sorted (every entry is
its manager's; without it a later duplicate's set, in the union but not covered by the
`keysWithItems` premise, can strip an item's key). -/
theorem prune_conforms' (S : Schema) (t : TypeRef) (merged : UVal) (mf : MF) (L : VSet)
    (hS : S.WF) (hc : conforms S t merged) (hs : keysSorted mf = true)
    (hkmf : ∀ m e, mf.get m = some e → keysWithItems S t e.set) (hkL : keysWithItems S t L.set)
    (hcL : schemaConsistent S t L.set) :
    let p0 := removeItems S t merged (ensureNamed S t L.set)
    let p1 := addBackOwnedMF S t merged p0 mf
    conforms S t p0 ∧ conforms S t p1 ∧ conforms S t (addBackDangling S t merged p1 L.set) := by
  intro p0 p1
  have nbaF : NoBelowAtomic S t (ensureNamed S t (fieldSet S t merged)) :=
    nba_ensureNamed (nba_fieldSet S t merged)
  -- pass 1
  have h0 : conforms S t p0 :=
    removeItems_conforms S hS t merged _ hc (kc_ensureNamed hkL)
      (nba_ensureNamed (nba_of_consistent hcL))
  -- pass 2
  have h1 : conforms S t p1 := by
    show conforms S t (addBackOwnedMF S t merged p0 mf)
    cases mf with
    | nil => exact h0
    | cons me mf' =>
      simp only [addBackOwnedMF, addBackOwned]
      apply removeItems_conforms S hS t merged _ hc
      · intro p fl n v hn h
        obtain ⟨hA, hB⟩ := mem_pdiff.1 h
        obtain ⟨-, hiF, hgr⟩ := item_facts S hS t merged hc hn hA
        refine mem_pdiff.2 ⟨ens_of_mem hiF, fun hi => ?_⟩
        rcases mem_punion.1 hi with hi | hi
        · have K0 := Glue.kwi_fieldSet S t p0 hS h0
          exact hB (mem_punion.2 (Or.inl (ens_of_mem ((K0 p fl).2.1 (ens_key hi) hgr n v hn))))
        · obtain ⟨me', hme', him⟩ := (Glue.mem_mfUnion _ _).1 (ens_key hi)
          have K := kwi_of_mem S t _ hs hkmf me' hme'
          exact hB (mem_punion.2 (Or.inr (ens_of_mem ((Glue.mem_mfUnion _ _).2
            ⟨me', hme', (K p fl).2.1 him hgr n v hn⟩))))
      · exact nba_mono (fun q hq => (mem_pdiff.1 hq).1) nbaF
  refine ⟨h0, h1, ?_⟩
  -- pass 3
  simp only [addBackDangling]
  apply removeItems_conforms S hS t merged _ hc
  · intro p fl n v hn h
    obtain ⟨hAB, hL⟩ := mem_pinter.1 h
    obtain ⟨hA, hB⟩ := mem_pdiff.1 hAB
    obtain ⟨-, hiF, hgr⟩ := item_facts S hS t merged hc hn hA
    refine mem_pinter.2 ⟨mem_pdiff.2 ⟨ens_of_mem hiF, fun hi => ?_⟩,
      kc_ensureNamed hkL p fl n v hn hL⟩
    have K1 := Glue.kwi_fieldSet S t p1 hS h1
    exact hB (ens_of_mem ((K1 p fl).2.1 (ens_key hi) hgr n v hn))
  · exact nba_mono (fun q hq => (mem_pdiff.1 (mem_pinter.1 hq).1).1) nbaF

/-! ## A reconciled set is consistent with the schema (`Apply`'s last set, `reconcileMF`) -/

theorem reconAt_append (S : Schema) : ∀ (p r : Path) (t : TypeRef),
    reconAt S t (p ++ r) = (reconAt S t p).bind (fun t' => reconAt S t' r)
  | [], _, _ => rfl
  | pe :: p, r, t => by
    simp only [List.cons_append, reconAt]
    split
    · split
      · next t' _ => exact reconAt_append S p r t'
      · rfl
    · rfl

theorem schemaConsistent_reconcile (S : Schema) (t : TypeRef) (s : PathSet) :
    schemaConsistent S t (reconcile S t s) := by
  unfold schemaConsistent
  rw [FSet_isEmpty_iff_law_holds]
  intro p hp
  obtain ⟨hpne, ⟨r, hr, hm⟩, t', ha, hat⟩ := (atomicNodes_mem_law_holds S t _ p).1 hp
  rcases (reconcile_mem_law_holds S t s _).1 hm with ⟨hs, hn⟩ | hm
  · exact hn ⟨p, (atomicNodes_mem_law_holds S t s p).2 ⟨hpne, ⟨r, hr, hs⟩, t', ha, hat⟩,
      List.prefix_append p r⟩
  · obtain ⟨-, -, t'', ha', -⟩ := (atomicNodes_mem_law_holds S t s _).1 hm
    obtain ⟨pe, r', rfl⟩ := List.exists_cons_of_ne_nil hr
    have hng : isGranularT S t' = false := by
      cases hg : isGranularT S t' with
      | false => rfl
      | true => rw [granular_not_atomic hg] at hat; cases hat
    rw [reconAt_append, ha] at ha'
    simp [reconAt, hng] at ha'

/-- `Apply`'s last set (the applier's reconciled entry) is consistent with the schema. -/
theorem reconcileMF_get_consistent (S : Schema) (t : TypeRef) (mf : MF) (m : GoString) (L : VSet)
    (h : (reconcileMF S t mf).get m = some L) : schemaConsistent S t L.set := by
  rw [reconcileMF_get_law_holds] at h
  obtain ⟨e, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact schemaConsistent_reconcile S t e.set

end Prune

/-- **`prune`'s passes keep the object conforming** (`merge/Laws.lean`, restated). -/
theorem prune_conforms_law_holds : prune_conforms.law :=
  fun S t merged mf L hS hc hs hkmf hkL hcL =>
    Prune.prune_conforms' S t merged mf L hS hc hs hkmf hkL hcL

end smd
end EtcdGrove
end Perennial
