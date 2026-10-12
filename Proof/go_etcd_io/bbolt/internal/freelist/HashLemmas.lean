/-
Pure lemmas about the `hashMap` freelist's maps (`HashModel.lean`): a consistent `hashMap`
(`hashOK`) stays consistent when a span is added (`addSpan`, `hashOK_add`) or deleted
(`delSpan`, `hashOK_del`), the free ids being determined by the spans (`PgidsIncr.ext`); the
spans' ids, gathered in any order of the starts, are the free ids up to order
(`spans_flat_perm`), and in increasing order of the starts exactly the free ids
(`spans_flat_eq`).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.HashModel
public import Proof.go_etcd_io.bbolt.internal.freelist.ArrayLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt.internal.freelist

/-- The ids, sorted. -/
def sortIds (l : List w64) : List w64 := l.mergeSort (fun a b => decide (uint.Z a ≤ uint.Z b))

/-- `sets` with `st` dropped from the set of size `sz`, and that set dropped if it is empty
(`delSpan`). -/
def setsDel (sets : GMap w64 (GMap w64 Unit)) (sz st : w64) : GMap w64 (GMap w64 Unit) :=
  if GMap.size (GMap.delete st ((sets !! sz).getD ∅)) = 0 then GMap.delete sz sets
  else <[sz := GMap.delete st ((sets !! sz).getD ∅)]> sets

/-- The size of the span starting at `k` (`0` if none). -/
def spanLen (sp : GMap w64 w64) (k : w64) : Nat := uint.nat ((sp !! k).getD 0)

/-- The ids of the span starting at `k`. -/
def spanRun (sp : GMap w64 w64) (k : w64) : List w64 := runIds k (spanLen sp k)

/-! ## Lists of ids -/

/-- Increasing lists with the same elements are equal. -/
theorem PgidsIncr.ext {l1 l2 : List w64} (h1 : PgidsIncr l1) (h2 : PgidsIncr l2)
    (hm : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 := by
  have hp : l1.Perm l2 := (List.perm_ext_iff_of_nodup h1.nodup h2.nodup).2 hm
  exact List.Perm.eq_of_pairwise (le := fun a b => uint.Z a ≤ uint.Z b)
    (fun a b _ _ h1 h2 => by word) (h1.imp Int.le_of_lt) (h2.imp Int.le_of_lt) hp

theorem perm_of_mem {l1 l2 : List w64} (h1 : l1.Nodup) (h2 : l2.Nodup)
    (hm : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1.Perm l2 :=
  (List.perm_ext_iff_of_nodup h1 h2).2 hm

theorem sortIds_perm (l : List w64) : (sortIds l).Perm l := List.mergeSort_perm _ _

theorem sortIds_incr {l : List w64} (h : l.Nodup) : PgidsIncr (sortIds l) := by
  have hm : (sortIds l).Pairwise (fun a b => decide (uint.Z a ≤ uint.Z b) = true) :=
    List.pairwise_mergeSort (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
      (fun a b => by
        rcases Int.le_total (uint.Z a) (uint.Z b) with h | h
        · simp only [decide_eq_true h, Bool.true_or]
        · simp only [decide_eq_true h, Bool.or_true]) l
  exact pgidsIncr_of_sorted_nodup (hm.imp fun h => by simpa using h)
    ((sortIds_perm l).nodup_iff.2 h)

theorem PgidsIncr.filter {l : List w64} (h : PgidsIncr l) (p : w64 → Bool) :
    PgidsIncr (l.filter p) :=
  List.Pairwise.sublist List.filter_sublist h

/-- The ids of a run all in a list without duplicates: the run's length of them. -/
theorem run_filter_length {free : List w64} {st : w64} {n : Nat} (hnd : free.Nodup)
    (hnw : uint.Z st + n ≤ 2 ^ 64) (hin : ∀ x, inRun st n x → x ∈ free) :
    (free.filter (fun x => decide (inRun st n x))).length = n := by
  have : (free.filter (fun x => decide (inRun st n x))).Perm (runIds st n) := by
    refine perm_of_mem (hnd.sublist List.filter_sublist) (runIds_nodup hnw) (fun x => ?_)
    rw [List.mem_filter, mem_runIds hnw, decide_eq_true_iff]
    exact ⟨fun h => h.2, fun h => ⟨hin x h, h⟩⟩
  rw [this.length_eq, runIds_length]

theorem filter_not_length {free : List w64} {st : w64} {n : Nat} (hnd : free.Nodup)
    (hnw : uint.Z st + n ≤ 2 ^ 64) (hin : ∀ x, inRun st n x → x ∈ free) :
    (free.filter (fun x => !decide (inRun st n x))).length = free.length - n := by
  have h1 := run_filter_length hnd hnw hin
  have h2 := (List.filter_append_perm (fun x => decide (inRun st n x)) free).length_eq
  simp only [List.length_append] at h2
  omega

/-! ## Spans -/

theorem span_mem {sp : GMap w64 w64} {free : List w64} (h : spansFree sp free) {st sz x : w64}
    (hs : sp !! st = some sz) (hx : inRun st (uint.nat sz) x) : x ∈ free :=
  (h.2 x).2 ⟨st, sz, hs, hx⟩

theorem hm_inRun_self {st : w64} {n : Nat} (h : 1 ≤ n) : inRun st n st := by
  unfold inRun; omega

/-- The last id of a span of size `sz ≥ 1` (not wrapping around) is in it. -/
theorem inRun_last {st sz : w64} (h1 : 1 ≤ uint.Z sz) (h2 : uint.Z st + uint.Z sz ≤ 2 ^ 64) :
    inRun st (uint.nat sz) (st + sz - W64 1) := by
  unfold inRun; constructor <;> word

theorem span_disj {sp : GMap w64 w64} (h : spansOK sp) {st sz st' sz' x : w64}
    (hs : sp !! st = some sz) (hs' : sp !! st' = some sz') (hx : inRun st (uint.nat sz) x)
    (hx' : inRun st' (uint.nat sz') x) : st = st' := by
  exact Classical.byContradiction fun hne => h.2 st sz st' sz' x hs hs' hne hx hx'

theorem span_le_len {sp : GMap w64 w64} {free : List w64} (hok : spansOK sp)
    (hf : spansFree sp free) {st sz : w64} (hs : sp !! st = some sz) :
    uint.nat sz ≤ free.length := by
  have := run_filter_length hf.1.nodup (st := st) (n := uint.nat sz)
    (by have := (hok.1 st sz hs).2; word) (fun x hx => span_mem hf hs hx)
  rw [← this]; exact List.length_filter_le _ _

/-- The free ids are at least `2`: a span's ids are at least `1`, so its start is. -/
theorem span_ge {sp : GMap w64 w64} {free : List w64} (hf : spansFree sp free)
    (hge : ∀ x ∈ free, 2 ≤ uint.Z x) {st sz x : w64} (hs : sp !! st = some sz)
    (hx : inRun st (uint.nat sz) x) : 2 ≤ uint.Z x :=
  hge x (span_mem hf hs hx)

/-! ## Deleting and adding a span -/

theorem lookup_delete_isSome {V : Type} (m : GMap w64 V) (k k' : w64) :
    (GMap.delete k m !! k').isSome ↔ k ≠ k' ∧ (m !! k').isSome := by
  rw [GMap.lookup_delete_iff]
  by_cases h : k = k'
  · simp [h]
  · simp [h]

theorem getD_lookup_isSome (o : Option (GMap w64 Unit)) (k : w64) :
    ((o.getD ∅) !! k).isSome ↔ ∃ set, o = some set ∧ (set !! k).isSome := by
  cases o with
  | none => simp
  | some s => simp

theorem setsDel_lookup (sets : GMap w64 (GMap w64 Unit)) (sz st sz' st' : w64) :
    (∃ set, setsDel sets sz st !! sz' = some set ∧ (set !! st').isSome) ↔
      (∃ set, sets !! sz' = some set ∧ (set !! st').isSome) ∧ ¬ (sz' = sz ∧ st' = st) := by
  unfold setsDel
  by_cases hz : sz = sz'
  · subst hz
    by_cases h0 : GMap.size (GMap.delete st ((sets !! sz).getD ∅)) = 0
    · rw [if_pos h0, GMap.lookup_delete]
      constructor
      · rintro ⟨set, hset, -⟩; cases hset
      · rintro ⟨⟨set, hset, hst⟩, hn⟩
        refine absurd ⟨rfl, Classical.byContradiction fun hne => ?_⟩ hn
        have := GMap.map_size_nonzero (GMap.delete st ((sets !! sz).getD ∅)) st'
          ((lookup_delete_isSome _ _ _).2 ⟨Ne.symm hne, by rw [hset]; exact hst⟩)
        omega
    · rw [if_neg h0, GMap.lookup_insert]
      constructor
      · rintro ⟨set, hset, hst⟩
        cases hset
        obtain ⟨hne, hs⟩ := (lookup_delete_isSome _ _ _).1 hst
        exact ⟨(getD_lookup_isSome _ _).1 hs, fun h => hne h.2.symm⟩
      · rintro ⟨hs, hn⟩
        refine ⟨_, rfl, (lookup_delete_isSome _ _ _).2 ⟨fun h => hn ⟨rfl, h.symm⟩, ?_⟩⟩
        exact (getD_lookup_isSome _ _).2 hs
  · have hn : ¬ (sz' = sz ∧ st' = st) := fun h => hz h.1.symm
    split
    · rw [GMap.lookup_delete_ne _ hz]; exact ⟨fun h => ⟨h, hn⟩, fun h => h.1⟩
    · rw [GMap.lookup_insert_ne _ _ hz]; exact ⟨fun h => ⟨h, hn⟩, fun h => h.1⟩

theorem setsDel_nonempty {sets : GMap w64 (GMap w64 Unit)} {sz st : w64}
    (h : ∀ sz set, sets !! sz = some set → ∃ st, (set !! st).isSome) :
    ∀ sz' set, setsDel sets sz st !! sz' = some set → ∃ st', (set !! st').isSome := by
  intro sz' set hs
  unfold setsDel at hs
  split at hs
  · by_cases hz : sz = sz'
    · subst hz; rw [GMap.lookup_delete] at hs; cases hs
    · rw [GMap.lookup_delete_ne _ hz] at hs; exact h sz' set hs
  · rename_i h0
    by_cases hz : sz = sz'
    · subst hz; rw [GMap.lookup_insert] at hs; cases hs
      obtain ⟨k, v, hv⟩ := (GMap.map_size_ne_0_lookup _).1 h0
      exact ⟨k, by rw [hv]; rfl⟩
    · rw [GMap.lookup_insert_ne _ _ hz] at hs; exact h sz' set hs

/-- Deleting the span at `st` (`delSpan`): its ids are no longer free. -/
theorem hashOK_del {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) {st sz : w64} (hst : sp !! st = some sz)
    (l' : List w64) (hl' : PgidsIncr l')
    (hm : ∀ x, x ∈ l' ↔ x ∈ free ∧ ¬ inRun st (uint.nat sz) x) :
    hashOK (cnt - sz) (GMap.delete st sp) (GMap.delete (st + (sz - W64 1)) bwm)
      (setsDel sets sz st) l' := by
  obtain ⟨⟨hsz, hdj⟩, hf, ⟨hb, hs, hne⟩, hc, hlen⟩ := h
  obtain ⟨hsz1, hnw⟩ := hsz st sz hst
  have hlast : st + (sz - W64 1) = st + sz - W64 1 := by word
  have hl'eq : l' = free.filter (fun x => !decide (inRun st (uint.nat sz) x)) :=
    PgidsIncr.ext hl' (hf.1.filter _) (fun x => by
      rw [hm x, List.mem_filter]; simp)
  have hlen' : l'.length = free.length - uint.nat sz := by
    rw [hl'eq]; exact filter_not_length hf.1.nodup (by word) (fun x hx => span_mem hf hst hx)
  have hle : uint.nat sz ≤ free.length := span_le_len ⟨hsz, hdj⟩ hf hst
  refine ⟨⟨fun st' sz' h' => ?_, fun s1 z1 s2 z2 x h1 h2 hne' => ?_⟩, ⟨hl', fun x => ?_⟩,
    ⟨fun k v => ?_, fun z s => ?_, setsDel_nonempty hne⟩, ?_, ?_⟩
  · rw [GMap.lookup_delete_iff] at h'; split at h'; · cases h'
    exact hsz st' sz' h'
  · rw [GMap.lookup_delete_iff] at h1 h2
    split at h1; · cases h1
    split at h2; · cases h2
    exact hdj s1 z1 s2 z2 x h1 h2 hne'
  · rw [hm x, (hf.2 x)]
    constructor
    · rintro ⟨⟨st', sz', hs', hx⟩, hn⟩
      refine ⟨st', sz', ?_, hx⟩
      have : st ≠ st' := by rintro rfl; rw [hst] at hs'; cases hs'; exact hn hx
      rw [GMap.lookup_delete_ne _ this]; exact hs'
    · rintro ⟨st', sz', hs', hx⟩
      rw [GMap.lookup_delete_iff] at hs'; split at hs'; · cases hs'
      rename_i hne'
      exact ⟨⟨st', sz', hs', hx⟩, fun hr => hdj st sz st' sz' x hst hs' hne' hr hx⟩
  · rw [hlast, GMap.lookup_delete_iff]
    split
    · rename_i hk
      simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro st' hs' hk'
      rw [GMap.lookup_delete_iff] at hs'; split at hs'; · cases hs'
      rename_i hne'
      obtain ⟨h1', h2'⟩ := hsz st' v hs'
      have e : st + sz - W64 1 = st' + v - W64 1 := hk.trans hk'
      have := span_disj ⟨hsz, hdj⟩ hst hs' (inRun_last hsz1 hnw) (by rw [e]; exact inRun_last h1' h2')
      exact hne' this
    · rename_i hk
      rw [hb k v]
      constructor
      · rintro ⟨st', hs', rfl⟩
        refine ⟨st', ?_, rfl⟩
        have : st ≠ st' := by rintro rfl; rw [hst] at hs'; cases hs'; exact hk rfl
        rw [GMap.lookup_delete_ne _ this]; exact hs'
      · rintro ⟨st', hs', rfl⟩
        rw [GMap.lookup_delete_iff] at hs'; split at hs'; · cases hs'
        exact ⟨st', hs', rfl⟩
  · rw [setsDel_lookup, hs z s, GMap.lookup_delete_iff]
    by_cases hss : st = s
    · subst hss; rw [if_pos rfl]
      constructor
      · rintro ⟨hz, hn⟩; rw [hst] at hz; cases hz; exact absurd ⟨rfl, rfl⟩ hn
      · intro h'; cases h'
    · rw [if_neg hss]
      exact ⟨fun h => h.1, fun h => ⟨h, fun h' => hss h'.2.symm⟩⟩
  · rw [hlen']
    have h1 : (uint.nat sz : Int) = uint.Z sz := by word
    have h2 : uint.Z sz ≤ uint.Z cnt := by rw [hc]; omega
    have : uint.Z (cnt - sz) = uint.Z cnt - uint.Z sz := by word
    rw [this, hc]; omega
  · omega

/-- Adding the span of `sz ≥ 1` ids from `st` (not wrapping around, none of them free;
`addSpan`): they are free now. -/
theorem hashOK_add {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) {st sz : w64} (hsz1 : 1 ≤ uint.Z sz)
    (hnw : uint.Z st + uint.Z sz ≤ 2 ^ 64)
    (hdis : ∀ x, inRun st (uint.nat sz) x → x ∉ free) (hlen' : free.length + uint.nat sz < 2 ^ 63)
    (l' : List w64) (hl' : PgidsIncr l')
    (hm : ∀ x, x ∈ l' ↔ x ∈ free ∨ inRun st (uint.nat sz) x) :
    hashOK (cnt + sz) (<[st := sz]> sp) (<[st - W64 1 + sz := sz]> bwm)
      (<[sz := <[st := ()]> ((sets !! sz).getD ∅)]> sets) l' := by
  obtain ⟨⟨hsz, hdj⟩, hf, ⟨hb, hs, hne⟩, hc, hlen⟩ := h
  have hlast : st - W64 1 + sz = st + sz - W64 1 := by word
  have hstn : sp !! st = none := by
    cases h' : sp !! st with
    | none => rfl
    | some z =>
      exact absurd (span_mem hf h' (hm_inRun_self (by have := (hsz st z h').1; word)))
        (hdis st (hm_inRun_self (by word)))
  -- a span's ids are not in the new run
  have hout : ∀ st' sz' x, sp !! st' = some sz' → inRun st' (uint.nat sz') x →
      ¬ inRun st (uint.nat sz) x := fun st' sz' x h1 h2 h3 => hdis x h3 (span_mem hf h1 h2)
  have hne_st : ∀ st' sz', sp !! st' = some sz' → st' ≠ st := by
    rintro st' sz' h1 rfl; rw [hstn] at h1; cases h1
  refine ⟨⟨fun st' sz' h' => ?_, fun s1 z1 s2 z2 x h1 h2 hne' => ?_⟩, ⟨hl', fun x => ?_⟩,
    ⟨fun k v => ?_, fun z s => ?_, fun z set hz => ?_⟩, ?_, ?_⟩
  · by_cases e : st = st'
    · subst e; rw [GMap.lookup_insert] at h'; cases h'; exact ⟨hsz1, hnw⟩
    · rw [GMap.lookup_insert_ne _ _ e] at h'; exact hsz st' sz' h'
  · by_cases e1 : st = s1
    · subst e1; rw [GMap.lookup_insert] at h1; cases h1
      rw [GMap.lookup_insert_ne _ _ hne'] at h2
      exact fun hx1 hx2 => hout s2 z2 x h2 hx2 hx1
    · rw [GMap.lookup_insert_ne _ _ e1] at h1
      by_cases e2 : st = s2
      · subst e2; rw [GMap.lookup_insert] at h2; cases h2
        exact hout s1 z1 x h1
      · rw [GMap.lookup_insert_ne _ _ e2] at h2
        exact hdj s1 z1 s2 z2 x h1 h2 hne'
  · rw [hm x, hf.2 x]
    constructor
    · rintro (⟨st', sz', h1, h2⟩ | h)
      · exact ⟨st', sz', by rw [GMap.lookup_insert_ne _ _ (hne_st st' sz' h1).symm]; exact h1, h2⟩
      · exact ⟨st, sz, GMap.lookup_insert _ _ _, h⟩
    · rintro ⟨st', sz', h1, h2⟩
      by_cases e : st = st'
      · subst e; rw [GMap.lookup_insert] at h1; cases h1; exact Or.inr h2
      · rw [GMap.lookup_insert_ne _ _ e] at h1; exact Or.inl ⟨st', sz', h1, h2⟩
  · rw [hlast]
    by_cases ek : st + sz - W64 1 = k
    · subst ek; rw [GMap.lookup_insert]
      constructor
      · intro e; cases e; exact ⟨st, GMap.lookup_insert _ _ _, rfl⟩
      · rintro ⟨st', h1, e⟩
        by_cases es : st = st'
        · subst es; rw [GMap.lookup_insert] at h1; cases h1; rfl
        · rw [GMap.lookup_insert_ne _ _ es] at h1
          obtain ⟨a1, a2⟩ := hsz st' v h1
          exact absurd (inRun_last hsz1 hnw) (hout st' v _ h1 (by rw [e]; exact inRun_last a1 a2))
    · rw [GMap.lookup_insert_ne _ _ ek, hb k v]
      constructor
      · rintro ⟨st', h1, e⟩
        exact ⟨st', by rw [GMap.lookup_insert_ne _ _ (hne_st st' v h1).symm]; exact h1, e⟩
      · rintro ⟨st', h1, e⟩
        by_cases es : st = st'
        · subst es; rw [GMap.lookup_insert] at h1; cases h1; exact absurd e.symm ek
        · rw [GMap.lookup_insert_ne _ _ es] at h1; exact ⟨st', h1, e⟩
  · by_cases ez : sz = z
    · subst ez
      rw [GMap.lookup_insert]
      simp only [Option.some.injEq, exists_eq_left']
      by_cases es : st = s
      · subst es; simp [GMap.lookup_insert]
      · rw [GMap.lookup_insert_ne _ _ es, GMap.lookup_insert_ne _ _ es, getD_lookup_isSome, hs]
    · rw [GMap.lookup_insert_ne _ _ ez, hs z s]
      by_cases es : st = s
      · subst es; rw [GMap.lookup_insert, hstn]; simpa using ez
      · rw [GMap.lookup_insert_ne _ _ es]
  · by_cases ez : sz = z
    · subst ez; rw [GMap.lookup_insert] at hz; cases hz
      exact ⟨st, by simp [GMap.lookup_insert]⟩
    · rw [GMap.lookup_insert_ne _ _ ez] at hz; exact hne z set hz
  · have hp : l'.Perm (free ++ runIds st (uint.nat sz)) := by
      refine perm_of_mem hl'.nodup ?_ (fun x => ?_)
      · rw [List.nodup_append]
        refine ⟨hf.1.nodup, runIds_nodup (by word), fun a ha b hb e => ?_⟩
        subst e; exact hdis a ((mem_runIds (by word)).1 hb) ha
      · rw [hm x, List.mem_append, mem_runIds (by word)]
    rw [hp.length_eq, List.length_append, runIds_length]
    have : uint.Z (cnt + sz) = uint.Z cnt + uint.Z sz := by
      have : uint.Z cnt + uint.Z sz < 2 ^ 64 := by rw [hc]; word
      word
    rw [this, hc]; word
  · have hp : l'.length ≤ free.length + uint.nat sz := by
      have hsub : ∀ x ∈ l', x ∈ free ++ runIds st (uint.nat sz) := fun x hx => by
        rw [List.mem_append, mem_runIds (by word)]; exact (hm x).1 hx
      have := List.Nodup.length_le_of_subset hl'.nodup hsub
      rw [List.length_append, runIds_length] at this; exact this
    omega

/-! ## The spans, gathered -/

theorem spanRun_mem {sp : GMap w64 w64} (hok : spansOK sp) {k x : w64}
    (hk : (sp !! k).isSome) : x ∈ spanRun sp k ↔ inRun k (spanLen sp k) x := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hk
  unfold spanRun spanLen; rw [hv, Option.getD_some]
  exact mem_runIds (by have := (hok.1 k v hv).2; word)

/-- The spans' ids, gathered in the order of a list of distinct starts. -/
theorem spans_flat_nodup {sp : GMap w64 w64} (hok : spansOK sp) {keys : List w64}
    (hnd : keys.Nodup) (hk : ∀ k ∈ keys, (sp !! k).isSome) :
    (keys.flatMap (spanRun sp)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun k hkm => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hk k hkm)
    unfold spanRun spanLen; rw [hv, Option.getD_some]
    exact runIds_nodup (by have := (hok.1 k v hv).2; word)
  · refine (List.nodup_iff_pairwise_ne.1 hnd).imp_of_mem (fun {a b} ha hb hne x hxa y hyb e => ?_)
    subst e
    have hka := hk a ha
    have hkb := hk b hb
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 hka
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.1 hkb
    have h1 := (spanRun_mem hok hka).1 hxa
    have h2 := (spanRun_mem hok hkb).1 hyb
    unfold spanLen at h1 h2; rw [hva, Option.getD_some] at h1; rw [hvb, Option.getD_some] at h2
    exact hok.2 a va b vb x hva hvb hne h1 h2

theorem spans_flat_mem {sp : GMap w64 w64} (hok : spansOK sp) {keys : List w64}
    (hk : ∀ k ∈ keys, (sp !! k).isSome) (x : w64) :
    x ∈ keys.flatMap (spanRun sp) ↔ ∃ k ∈ keys, ∃ sz, sp !! k = some sz ∧ inRun k (uint.nat sz) x := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨k, hkm, hx⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hk k hkm)
    have := (spanRun_mem hok (hk k hkm)).1 hx
    unfold spanLen at this; rw [hv, Option.getD_some] at this
    exact ⟨k, hkm, v, hv, this⟩
  · rintro ⟨k, hkm, v, hv, hx⟩
    refine ⟨k, hkm, (spanRun_mem hok (hk k hkm)).2 ?_⟩
    unfold spanLen; rw [hv, Option.getD_some]; exact hx

/-- The spans' ids, gathered in the order of any list of the starts (as a `range` over
`forwardMap` visits them): the free ids, up to order. -/
theorem spans_flat_perm {sp : GMap w64 w64} {free : List w64} (hok : spansOK sp)
    (hf : spansFree sp free) {keys : List w64} (hnd : keys.Nodup)
    (hk : ∀ k, k ∈ keys ↔ (sp !! k).isSome) : (keys.flatMap (spanRun sp)).Perm free := by
  have hk' : ∀ k ∈ keys, (sp !! k).isSome := fun k h => (hk k).1 h
  refine perm_of_mem (spans_flat_nodup hok hnd hk') hf.1.nodup (fun x => ?_)
  rw [spans_flat_mem hok hk', hf.2 x]
  constructor
  · rintro ⟨k, -, v, hv, hx⟩; exact ⟨k, v, hv, hx⟩
  · rintro ⟨k, v, hv, hx⟩; exact ⟨k, (hk k).2 (by simp [hv]), v, hv, hx⟩

/-- The sizes of the spans add up to the number of free ids. -/
theorem spans_sum {sp : GMap w64 w64} {free : List w64} (hok : spansOK sp)
    (hf : spansFree sp free) {keys : List w64} (hnd : keys.Nodup)
    (hk : ∀ k, k ∈ keys ↔ (sp !! k).isSome) : (keys.map (spanLen sp)).sum = free.length := by
  rw [← (spans_flat_perm hok hf hnd hk).length_eq, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro k _; unfold spanRun; rw [runIds_length]

theorem runIds_incr {st : w64} {n : Nat} (h : uint.Z st + n ≤ 2 ^ 64) : PgidsIncr (runIds st n) := by
  unfold PgidsIncr runIds
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := n)).imp_of_mem (fun {a b} ha hb hab => ?_)
  simp only [List.mem_range] at ha hb
  word

/-- The spans' ids, gathered in increasing order of the starts: exactly the free ids. -/
theorem spans_flat_eq {sp : GMap w64 w64} {free : List w64} (hok : spansOK sp)
    (hf : spansFree sp free) {keys : List w64} (hinc : PgidsIncr keys)
    (hk : ∀ k, k ∈ keys ↔ (sp !! k).isSome) : keys.flatMap (spanRun sp) = free := by
  have hk' : ∀ k ∈ keys, (sp !! k).isSome := fun k h => (hk k).1 h
  refine PgidsIncr.ext ?_ hf.1 (fun x => (spans_flat_perm hok hf hinc.nodup hk).mem_iff)
  unfold PgidsIncr
  rw [List.pairwise_flatMap]
  refine ⟨fun k hkm => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hk' k hkm)
    unfold spanRun spanLen; rw [hv, Option.getD_some]
    exact runIds_incr (by have := (hok.1 k v hv).2; word)
  · refine hinc.imp_of_mem (fun {a b} ha hb hab x hx y hy => ?_)
    obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 (hk' a ha)
    obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.1 (hk' b hb)
    have h1 := (spanRun_mem hok (hk' a ha)).1 hx
    have h2 := (spanRun_mem hok (hk' b hb)).1 hy
    unfold spanLen at h1 h2; rw [hva, Option.getD_some] at h1; rw [hvb, Option.getD_some] at h2
    have hb1 : 1 ≤ uint.Z vb := (hok.1 b vb hvb).1
    refine Classical.byContradiction fun hlt => ?_
    -- `b` is then in `a`'s span
    have hbin : inRun a (uint.nat va) b := by unfold inRun at h1 h2 ⊢; omega
    exact hok.2 a va b vb b hva hvb (by rintro rfl; omega) hbin (hm_inRun_self (by word))

/-- A map whose keys are all in a set of `freemaps` has fewer than `2^63` of them (the set's
keys are starts of spans: free ids). -/
theorem setsDel_size_lt {cnt : w64} {sp bwm : GMap w64 w64} {sets : GMap w64 (GMap w64 Unit)}
    {free : List w64} (h : hashOK cnt sp bwm sets free) {sz : w64} {set : GMap w64 Unit}
    (hset : sets !! sz = some set) {V : Type} (m : GMap w64 V)
    (hm : ∀ k, (m !! k).isSome → (set !! k).isSome) : GMap.size m < 2 ^ 63 := by
  obtain ⟨⟨hsz, -⟩, hf, ⟨-, hs, -⟩, -, hlen⟩ := h
  have hsub : m.domList ⊆ free := by
    intro k hk
    have hsp := (hs sz k).1 ⟨set, hset, hm k ((GMap.mem_dom_list m k).1 hk)⟩
    exact span_mem hf hsp (hm_inRun_self (by have := (hsz k sz hsp).1; word))
  have := List.Nodup.length_le_of_subset (GMap.nodup_dom_list m) hsub
  rw [GMap.size_eq_dom_list_length]; omega

end bbolt
end EtcdGrove
end Perennial
