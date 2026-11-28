/-
(hraft_robust R3) The disk's image changes, as pure functions shaped like `disk.go`'s loops, and the two
contracts' abstractions (`absL`, `absS`) under them: `insEnt` (`insert`) gives `LogAbs.ins`/`LogAbs.store`,
`delEnts` (`DeleteRange`'s filter) `LogAbs.del` with the largest index left (`maxKey`), `setKV` (`Set`,
`SetUint64`) `GMap.insert`; `DiskImg.hi` is the largest key; the first entry's index the smallest.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Defs

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open github_com.hashicorp.raft proto

/-! ## Orderly indexes -/

/-- `IdxOk` as a pairwise order. -/
theorem idxOk_iff (es : List DEnt) :
    IdxOk es ↔ (∀ e ∈ es, 1 ≤ uint.nat e.idx) ∧ es.Pairwise (fun a b => uint.nat a.idx < uint.nat b.idx) := by
  induction es with
  | nil => simp [IdxOk]
  | cons e es ih =>
    cases es with
    | nil => simp [IdxOk]
    | cons f fs =>
      simp only [IdxOk, ih, List.mem_cons, forall_eq_or_imp, List.pairwise_cons]
      constructor
      · rintro ⟨h1, h2, ⟨h3, h4⟩, h5, h6⟩
        refine ⟨⟨h1, h3, h4⟩, ⟨h2, fun x hx => ?_⟩, h5, h6⟩
        exact Nat.lt_trans h2 (h5 x hx)
      · rintro ⟨⟨h1, h3, h4⟩, ⟨h2, _⟩, h5, h6⟩
        exact ⟨h1, h2, ⟨h3, h4⟩, h5, h6⟩

/-! ## Maps of lists -/

theorem ofList_isSome {V : Type} (l : List (Nat × V)) (k : Nat) :
    ((GMap.ofList l).lookup k).isSome ↔ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [GMap.ofList]; rfl
  | cons p l ih =>
    obtain ⟨a, v⟩ := p
    simp only [GMap.ofList, List.map_cons, List.mem_cons]
    by_cases h : a = k
    · subst h; simp [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ h, ih]; constructor
      · intro h'; exact Or.inr h'
      · rintro (h' | h'); exact absurd h'.symm h; exact h'

theorem ofList_lookup_none {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) (h : k ∉ l.map Prod.fst) :
    (GMap.ofList l).lookup k = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [GMap.ofList]
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h.1)]; exact ih h.2

theorem ofList_append_new {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) (v : V)
    (h : k ∉ l.map Prod.fst) : GMap.ofList (l ++ [(k, v)]) = GMap.insert k v (GMap.ofList l) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, w⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.cons_append, GMap.ofList]
    rw [ih h.2, GMap.insert_commute _ _ _ (Ne.symm h.1)]

theorem ofList_filter {K V : Type} [DecidableEq K] (l : List (K × V)) (P : K → Bool) :
    GMap.ofList (l.filter (fun p => P p.1)) = GMap.filter (fun k _ => P k) (GMap.ofList l) := by
  induction l with
  | nil => apply GMap.ext; intro k; simp [GMap.ofList]; rfl
  | cons p l ih =>
    obtain ⟨a, w⟩ := p
    apply GMap.ext; intro k
    by_cases hp : P a = true
    · simp only [List.filter_cons, hp, ↓reduceIte, GMap.ofList, GMap.lookup_filter]
      by_cases hk : a = k
      · subst hk; simp [GMap.lookup_insert, hp]; rfl
      · rw [GMap.lookup_insert_ne _ _ hk, GMap.lookup_insert_ne _ _ hk, ih, GMap.lookup_filter]
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, GMap.ofList, GMap.lookup_filter]
      by_cases hk : a = k
      · subst hk; rw [GMap.lookup_insert, ih, GMap.lookup_filter]; simp [hp]
      · rw [GMap.lookup_insert_ne _ _ hk, ih, GMap.lookup_filter]

/-! ## The log's index map -/

/-- The log's bindings. -/
def entsB (es : List DEnt) : List (Nat × Entry) := es.map fun e => (uint.nat e.idx, entOf e)

theorem logM_eq (I : DiskImg) : I.logM = GMap.ofList (entsB I.ents) := rfl

theorem entsB_keys (es : List DEnt) : (entsB es).map Prod.fst = es.map (fun e => uint.nat e.idx) := by
  simp [entsB]

/-! ## `insert` -/

/-- `insert`'s position: the entries below `x`. -/
def insPos (x : w64) (es : List DEnt) : Nat :=
  (es.takeWhile (fun f => decide (uint.nat f.idx < uint.nat x))).length

/-- **`insert(e)`**, as the Go loop does it. -/
def insEnt (e : DEnt) (es : List DEnt) : List DEnt :=
  if (es[insPos e.idx es]?.map DEnt.idx) = some e.idx then es.set (insPos e.idx es) e
  else es.take (insPos e.idx es) ++ e :: es.drop (insPos e.idx es)

/-- `insert`, recursively. -/
def insR (e : DEnt) : List DEnt → List DEnt
  | [] => [e]
  | f :: fs => if uint.nat f.idx < uint.nat e.idx then f :: insR e fs
      else if f.idx = e.idx then e :: fs else e :: f :: fs

theorem insEnt_eq (e : DEnt) (es : List DEnt) : insEnt e es = insR e es := by
  induction es with
  | nil => simp [insEnt, insPos, insR]
  | cons f fs ih =>
    unfold insEnt at ih ⊢
    by_cases h : uint.nat f.idx < uint.nat e.idx
    · have hp : insPos e.idx (f :: fs) = insPos e.idx fs + 1 := by
        simp [insPos, List.takeWhile_cons, h]
      have hne : f.idx ≠ e.idx := by intro h'; rw [h'] at h; omega
      rw [hp]; simp only [insR, h, ↓reduceIte, List.getElem?_cons_succ, List.set_cons_succ,
        List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [← ih]; split <;> rfl
    · have hp : insPos e.idx (f :: fs) = 0 := by simp [insPos, List.takeWhile_cons, h]
      rw [hp]; simp only [insR, h, ↓reduceIte, List.getElem?_cons_zero, Option.map_some,
        Option.some.injEq, List.set_cons_zero, List.take_zero, List.drop_zero, List.nil_append]

theorem insR_mem (e : DEnt) (es : List DEnt) (x : DEnt) (h : x ∈ insR e es) : x = e ∨ x ∈ es := by
  induction es with
  | nil => simp [insR] at h; exact Or.inl h
  | cons f fs ih =>
    unfold insR at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr List.mem_cons_self
      · rcases ih h with h | h; exact Or.inl h; exact Or.inr (List.mem_cons_of_mem _ h)
    · split at h
      · rcases List.mem_cons.1 h with h | h; exact Or.inl h; exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.1 h with h | h; exact Or.inl h; exact Or.inr h

theorem insR_ok (e : DEnt) (es : List DEnt) (he : 1 ≤ uint.nat e.idx) (h : IdxOk es) : IdxOk (insR e es) := by
  rw [idxOk_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases insR_mem e es x hx with rfl | hx; exact he; exact h1 x hx
  induction es with
  | nil => simp [insR]
  | cons f fs ih =>
    rw [List.pairwise_cons] at h2
    unfold insR
    split
    · rename_i hlt
      refine List.pairwise_cons.2 ⟨fun x hx => ?_, ih (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) h2.2⟩
      rcases insR_mem e fs x hx with rfl | hx; exact hlt; exact h2.1 x hx
    · rename_i hlt
      split
      · rename_i heq
        refine List.pairwise_cons.2 ⟨fun x hx => ?_, h2.2⟩
        rw [← heq]; exact h2.1 x hx
      · rename_i hne
        have : uint.nat e.idx < uint.nat f.idx := by
          have : uint.nat f.idx ≠ uint.nat e.idx := fun h' => hne (by word)
          omega
        refine List.pairwise_cons.2 ⟨fun x hx => ?_, List.pairwise_cons.2 h2⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact this
        · exact Nat.lt_trans this (h2.1 x hx)

theorem insR_logM (e : DEnt) (es : List DEnt) :
    GMap.ofList (entsB (insR e es)) = GMap.insert (uint.nat e.idx) (entOf e) (GMap.ofList (entsB es)) := by
  induction es with
  | nil => rfl
  | cons f fs ih =>
    unfold insR
    split
    · rename_i hlt
      simp only [entsB, List.map_cons, GMap.ofList] at ih ⊢
      rw [ih, GMap.insert_commute _ _ _ (by omega)]
    · split
      · rename_i _ heq
        simp only [entsB, List.map_cons, GMap.ofList]
        rw [heq, GMap.insert_insert]
      · rfl

/-- The largest index (`0` for none). -/
def maxIdx (es : List DEnt) : Nat := (es.map fun e => uint.nat e.idx).foldr Max.max 0

theorem maxIdx_cons (e : DEnt) (es : List DEnt) : maxIdx (e :: es) = Max.max (uint.nat e.idx) (maxIdx es) := rfl

theorem insR_maxIdx (e : DEnt) (es : List DEnt) : maxIdx (insR e es) = Max.max (uint.nat e.idx) (maxIdx es) := by
  induction es with
  | nil => simp [insR, maxIdx]
  | cons f fs ih =>
    unfold insR
    split
    · rw [maxIdx_cons, ih, maxIdx_cons]; omega
    · split
      · rename_i heq; rw [maxIdx_cons, maxIdx_cons, heq]; omega
      · rw [maxIdx_cons, maxIdx_cons]

theorem le_maxIdx (es : List DEnt) (e : DEnt) (h : e ∈ es) : uint.nat e.idx ≤ maxIdx es := by
  induction es with
  | nil => simp at h
  | cons f fs ih =>
    rw [maxIdx_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- `hi` is the largest index. -/
theorem hi_maxIdx (I : DiskImg) (h : IdxOk I.ents) : uint.nat I.hi = maxIdx I.ents := by
  unfold DiskImg.hi
  generalize I.ents = es at h ⊢
  induction es with
  | nil => simp [maxIdx]
  | cons f fs ih =>
    cases fs with
    | nil => simp [maxIdx]
    | cons g gs =>
      simp only [IdxOk] at h
      rw [List.getLast?_cons_cons, ih h.2.2, maxIdx_cons f (g :: gs)]
      have := le_maxIdx (g :: gs) g List.mem_cons_self
      omega

theorem maxIdx_lt (es : List DEnt) : maxIdx es < 2 ^ 64 := by
  induction es with
  | nil => simp [maxIdx]
  | cons f fs ih => rw [maxIdx_cons]; have := f.idx.isLt; simp [uint.nat] at *; omega

/-- The image's `hi` from the largest index. -/
def hiOf (es : List DEnt) : w64 := W64 (maxIdx es)

theorem hi_eq_hiOf (I : DiskImg) (h : IdxOk I.ents) : I.hi = hiOf I.ents := by
  have := hi_maxIdx I h
  have := maxIdx_lt I.ents
  unfold hiOf; word

/-! ### `StoreLogs`: inserting the entries at `first..` -/

/-- The entry `insert` stores for the Go value at index `k`. -/
def mkEnt (k : Nat) (e : Entry) (ty : w8) (ext : List w8) : DEnt :=
  ⟨W64 k, W64 e.term, ty, e.data, ext⟩

/-- Folding insertions. -/
def insAll (es : List DEnt) (ds : List DEnt) : List DEnt := ds.foldl (fun acc d => insR d acc) es

theorem insAll_logM (es ds : List DEnt) :
    GMap.ofList (entsB (insAll es ds)) =
      ds.foldl (fun m d => GMap.insert (uint.nat d.idx) (entOf d) m) (GMap.ofList (entsB es)) := by
  induction ds generalizing es with
  | nil => rfl
  | cons d ds ih => simp only [insAll, List.foldl_cons] at ih ⊢; rw [ih, insR_logM]

theorem insAll_ok (es ds : List DEnt) (hd : ∀ d ∈ ds, 1 ≤ uint.nat d.idx) (h : IdxOk es) :
    IdxOk (insAll es ds) := by
  induction ds generalizing es with
  | nil => exact h
  | cons d ds ih =>
    simp only [insAll, List.foldl_cons] at ih ⊢
    exact ih _ (fun x hx => hd x (List.mem_cons_of_mem _ hx)) (insR_ok d es (hd d List.mem_cons_self) h)

theorem insAll_maxIdx (es ds : List DEnt) :
    maxIdx (insAll es ds) = Max.max (maxIdx ds) (maxIdx es) := by
  induction ds generalizing es with
  | nil => simp [insAll, maxIdx]
  | cons d ds ih =>
    simp only [insAll, List.foldl_cons] at ih ⊢
    rw [ih, insR_maxIdx, maxIdx_cons]; omega

/-- The insertions `StoreLogs` makes, at `first + k`: a list of entries whose `entOf` are `es`. -/
def StoredAs (first : Nat) (es : RLog) (ds : List DEnt) : Prop :=
  ds.length = es.length ∧ ∀ k d, ds[k]? = some d → uint.nat d.idx = first + k ∧ es[k]? = some (entOf d)

theorem foldl_ins (m : GMap Nat Entry) (first : Nat) (es : RLog) (ds : List DEnt) (h : StoredAs first es ds) :
    ds.foldl (fun m d => GMap.insert (uint.nat d.idx) (entOf d) m) m = LogAbs.ins m first es := by
  induction ds generalizing m first es with
  | nil => obtain ⟨h1, _⟩ := h; cases es; rfl; simp at h1
  | cons d ds ih =>
    obtain ⟨h1, h2⟩ := h
    cases es with
    | nil => simp at h1
    | cons e es =>
      obtain ⟨hk, he⟩ := h2 0 d rfl
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      simp only [List.foldl_cons, LogAbs.ins]
      rw [hk, ← he, Nat.add_zero]
      apply ih
      refine ⟨by simpa using h1, fun k d' hd' => ?_⟩
      obtain ⟨a, b⟩ := h2 (k + 1) d' (by simpa using hd')
      exact ⟨by omega, by simpa using b⟩

theorem maxIdx_stored (first : Nat) (es : RLog) (ds : List DEnt) (h : StoredAs first es ds) (hne : es ≠ []) :
    maxIdx ds = first + es.length - 1 := by
  obtain ⟨h1, h2⟩ := h
  have hb : ∀ d ∈ ds, uint.nat d.idx ≤ first + es.length - 1 := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have := (h2 k _ (List.getElem?_eq_getElem hk)).1; omega
  have hlast : ∃ d ∈ ds, uint.nat d.idx = first + es.length - 1 := by
    have hl : es.length - 1 < ds.length := by
      have : es.length ≠ 0 := by simpa using hne
      omega
    refine ⟨ds[es.length - 1], List.getElem_mem hl, ?_⟩
    have := (h2 _ _ (List.getElem?_eq_getElem hl)).1; omega
  obtain ⟨d, hd, hdv⟩ := hlast
  have hle := le_maxIdx ds d hd
  have hge : maxIdx ds ≤ first + es.length - 1 := by
    clear hd hdv hle h2 h1
    induction ds with
    | nil => simp [maxIdx]
    | cons x xs ih =>
      rw [maxIdx_cons]
      have := hb x List.mem_cons_self
      have := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)); omega
  omega

/-- **`StoreLogs`'s image**: the entries inserted, the staged index written. -/
def storeImg (I : DiskImg) (ds : List DEnt) (stg : w64) : DiskImg :=
  { I with ents := insAll I.ents ds, commit := stg }

theorem storeImg_absL (I : DiskImg) (stg : w64) (first : Nat) (es : RLog) (ds : List DEnt)
    (hok : IdxOk I.ents) (h : StoredAs first es ds) (hb : first + es.length < 2 ^ 64) (hd : ∀ d ∈ ds, 1 ≤ uint.nat d.idx) :
    (storeImg I ds stg).absL stg = (I.absL stg).store first es ∧ IdxOk (storeImg I ds stg).ents := by
  have hok' := insAll_ok I.ents ds hd hok
  refine ⟨?_, hok'⟩
  unfold DiskImg.absL LogAbs.store
  simp only [storeImg]
  congr 1
  · simp only [DiskImg.logM]
    rw [show (insAll I.ents ds).map (fun e => (uint.nat e.idx, entOf e)) = entsB (insAll I.ents ds) from rfl,
      insAll_logM, foldl_ins _ first es ds h]; rfl
  · rw [show DiskImg.hi { I with ents := insAll I.ents ds, commit := stg } =
        DiskImg.hi ⟨insAll I.ents ds, I.kv, I.ikv, stg⟩ from rfl]
    rw [hi_eq_hiOf ⟨insAll I.ents ds, I.kv, I.ikv, stg⟩ hok', hi_eq_hiOf I hok]
    unfold hiOf
    simp only
    rw [insAll_maxIdx]
    have hmI := maxIdx_lt I.ents
    by_cases hne : es = []
    · subst hne
      have : ds = [] := by have := h.1; simpa using this
      subst this; simp [maxIdx]
    · rw [maxIdx_stored first es ds h hne]
      simp only [hne, ↓reduceIte]
      split
      · rename_i hlt
        have : uint.nat (W64 (maxIdx I.ents)) = maxIdx I.ents := by word
        rw [this] at hlt
        congr 1; omega
      · rename_i hlt
        have : uint.nat (W64 (maxIdx I.ents)) = maxIdx I.ents := by word
        rw [this] at hlt
        congr 1; omega

/-! ## `DeleteRange` -/

/-- **`DeleteRange(mn, mx)`'s entries**: those outside `mn..mx`. -/
def delEnts (mn mx : w64) (es : List DEnt) : List DEnt :=
  es.filter fun e => decide (¬ (uint.nat mn ≤ uint.nat e.idx ∧ uint.nat e.idx ≤ uint.nat mx))

/-- The largest key of a map (`0` for the empty one). -/
def maxKey (m : GMap Nat Entry) : w64 := W64 ((m.domList.foldr (Max.max : Nat → Nat → Nat) 0 : Nat) : Int)

theorem foldr_max_eq (l : List Nat) (n : Nat) (hle : ∀ x ∈ l, x ≤ n) (hmem : n ∈ l ∨ n = 0) :
    l.foldr Max.max 0 = n := by
  have h1 : l.foldr Max.max 0 ≤ n := by
    clear hmem
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldr_cons]
      have := hle x List.mem_cons_self
      have := ih (fun y hy => hle y (List.mem_cons_of_mem _ hy)); omega
  have h2 : ∀ x ∈ l, x ≤ l.foldr Max.max 0 := by
    intro x hx
    clear hle hmem h1
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := ih hx; omega
  rcases hmem with h | h
  · have := h2 n h; omega
  · omega

theorem maxKey_ofList (es : List DEnt) :
    uint.nat (maxKey (GMap.ofList (entsB es))) = maxIdx es := by
  have hm := maxIdx_lt es
  have : (GMap.ofList (entsB es)).domList.foldr Max.max 0 = maxIdx es := by
    apply foldr_max_eq
    · intro x hx
      rw [GMap.mem_dom_list, ofList_isSome, entsB_keys] at hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      exact le_maxIdx es e he
    · cases es with
      | nil => right; rfl
      | cons f fs =>
        left
        rw [GMap.mem_dom_list, ofList_isSome, entsB_keys]
        have : ∀ (l : List DEnt), l ≠ [] → maxIdx l ∈ l.map (fun e => uint.nat e.idx) := by
          intro l hl
          induction l with
          | nil => exact absurd rfl hl
          | cons x xs ih =>
            rw [maxIdx_cons, List.map_cons]
            cases xs with
            | nil => simp [maxIdx]
            | cons y ys =>
              have := ih (by simp)
              by_cases hxy : maxIdx (y :: ys) ≤ uint.nat x.idx
              · rw [Nat.max_eq_left hxy]; exact List.mem_cons_self
              · rw [Nat.max_eq_right (by omega)]; exact List.mem_cons_of_mem _ this
        exact this _ (by simp)
  unfold maxKey; rw [this]; word

/-- **`DeleteRange`'s image.** -/
def delImg (I : DiskImg) (mn mx : w64) : DiskImg := { I with ents := delEnts mn mx I.ents }

theorem delImg_absL (I : DiskImg) (stg mn mx : w64) (hok : IdxOk I.ents) :
    (delImg I mn mx).absL stg =
      (I.absL stg).delete (uint.nat mn) (uint.nat mx)
        (maxKey (LogAbs.del (I.absL stg).m (uint.nat mn) (uint.nat mx))) ∧ IdxOk (delImg I mn mx).ents := by
  have hok' : IdxOk (delEnts mn mx I.ents) := by
    rw [idxOk_iff] at hok ⊢
    exact ⟨fun x hx => hok.1 x (List.mem_filter.1 hx).1, hok.2.filter _⟩
  have hm : GMap.ofList (entsB (delEnts mn mx I.ents)) =
      LogAbs.del (GMap.ofList (entsB I.ents)) (uint.nat mn) (uint.nat mx) := by
    unfold LogAbs.del delEnts entsB
    refine Eq.trans ?_ (ofList_filter (I.ents.map fun e => (uint.nat e.idx, entOf e))
      (fun k => decide (¬(uint.nat mn ≤ k ∧ k ≤ uint.nat mx))))
    rw [List.filter_map]; rfl
  refine ⟨?_, hok'⟩
  unfold DiskImg.absL LogAbs.delete
  simp only
  rw [show (delImg I mn mx).logM = GMap.ofList (entsB (delEnts mn mx I.ents)) from rfl, hm]
  rw [show I.logM = GMap.ofList (entsB I.ents) from rfl, ← hm]
  congr 1
  rw [show (delImg I mn mx).hi = DiskImg.hi ⟨delEnts mn mx I.ents, I.kv, I.ikv, I.commit⟩ from rfl,
    hi_eq_hiOf ⟨delEnts mn mx I.ents, I.kv, I.ikv, I.commit⟩ hok']
  unfold hiOf
  have := maxKey_ofList (delEnts mn mx I.ents)
  have := maxIdx_lt (delEnts mn mx I.ents)
  simp only
  word

/-! ## The stable store's association lists -/

/-- **`Set`/`SetUint64`'s list**: the value of an equal key replaced, else the pair appended. -/
def setKV {V : Type} (k : List w8) (v : V) (kv : List (List w8 × V)) : List (List w8 × V) :=
  if k ∈ kv.map Prod.fst then kv.map (fun p => if p.1 = k then (p.1, v) else p) else kv ++ [(k, v)]

theorem map_upd_ne {V : Type} (k k' : List w8) (v : V) (kv : List (List w8 × V)) (h : k' ≠ k) :
    (GMap.ofList (kv.map (fun p => if p.1 = k then (p.1, v) else p))).lookup k' = (GMap.ofList kv).lookup k' := by
  induction kv with
  | nil => rfl
  | cons p kv ih =>
    obtain ⟨a, w⟩ := p
    simp only [List.map_cons, GMap.ofList]
    by_cases ha : a = k
    · subst ha
      simp only [↓reduceIte, GMap.ofList]
      rw [GMap.lookup_insert_ne _ _ (Ne.symm h), GMap.lookup_insert_ne _ _ (Ne.symm h), ih]
    · simp only [ha, ↓reduceIte, GMap.ofList]
      by_cases hk : a = k'
      · subst hk; rw [GMap.lookup_insert, GMap.lookup_insert]
      · rw [GMap.lookup_insert_ne _ _ hk, GMap.lookup_insert_ne _ _ hk, ih]

theorem map_upd_eq {V : Type} (k : List w8) (v : V) (kv : List (List w8 × V)) (h : k ∈ kv.map Prod.fst) :
    (GMap.ofList (kv.map (fun p => if p.1 = k then (p.1, v) else p))).lookup k = some v := by
  induction kv with
  | nil => simp at h
  | cons p kv ih =>
    obtain ⟨a, w⟩ := p
    simp only [List.map_cons, GMap.ofList]
    by_cases ha : a = k
    · subst ha; simp only [↓reduceIte, GMap.ofList]; rw [GMap.lookup_insert]
    · simp only [ha, ↓reduceIte, GMap.ofList]
      rw [GMap.lookup_insert_ne _ _ ha]
      apply ih
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h; exact absurd h.symm ha; exact h

theorem setKV_ofList {V : Type} (k : List w8) (v : V) (kv : List (List w8 × V)) :
    GMap.ofList (setKV k v kv) = GMap.insert k v (GMap.ofList kv) := by
  unfold setKV
  split
  · rename_i hmem
    apply GMap.ext; intro k'
    by_cases hk : k = k'
    · subst hk; rw [GMap.lookup_insert]; exact map_upd_eq k v kv hmem
    · rw [GMap.lookup_insert_ne _ _ hk]; exact map_upd_ne k k' v kv (Ne.symm hk)
  · rename_i hmem; exact ofList_append_new kv k v hmem

theorem setKV_keys {V : Type} (k : List w8) (v : V) (kv : List (List w8 × V)) (h : (kv.map Prod.fst).Nodup) :
    ((setKV k v kv).map Prod.fst).Nodup := by
  unfold setKV
  split
  · rw [List.map_map]
    have : (Prod.fst ∘ fun p : List w8 × V => if p.1 = k then (p.1, v) else p) = Prod.fst := by
      funext p; simp only [Function.comp]; split <;> rfl
    rw [this]; exact h
  · rename_i hmem
    rw [List.map_append, List.nodup_append]
    refine ⟨h, by simp, fun a ha b hb => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb; intro e; subst e; exact hmem ha

/-- The value of the first equal key (`Get`, `GetUint64`'s loops). -/
theorem ofList_lookup_first {K V : Type} [DecidableEq K] (kv : List (K × V)) (i : Nat) (p : K × V)
    (hp : kv[i]? = some p) (hfirst : ∀ j < i, ∀ q, kv[j]? = some q → q.1 ≠ p.1) :
    (GMap.ofList kv).lookup p.1 = some p.2 := by
  induction kv generalizing i with
  | nil => simp at hp
  | cons q kv ih =>
    obtain ⟨a, w⟩ := q
    simp only [GMap.ofList]
    cases i with
    | zero => simp at hp; subst hp; simp [GMap.lookup_insert]
    | succ i =>
      have hne := hfirst 0 (by omega) (a, w) rfl
      rw [GMap.lookup_insert_ne _ _ hne]
      exact ih i (by simpa using hp) (fun j hj q hq => hfirst (j + 1) (by omega) q (by simpa using hq))

theorem ofList_lookup_none' {K V : Type} [DecidableEq K] (kv : List (K × V)) (k : K)
    (h : ∀ q ∈ kv, q.1 ≠ k) : (GMap.ofList kv).lookup k = none := by
  apply ofList_lookup_none
  intro hm
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
  exact h q hq rfl

/-! ### The stable store's loops -/

theorem dk_kv_skip {V : Type} (kv : List (List w8 × V)) (i : Nat) (p : List w8 × V) (kb : List w8)
    (hp : kv[i]? = some p) (hne : p.1 ≠ kb) (h : ∀ j < i, ∀ q, kv[j]? = some q → q.1 ≠ kb) :
    ∀ j < i + 1, ∀ q, kv[j]? = some q → q.1 ≠ kb := by
  intro j hj q hq
  by_cases hji : j = i
  · subst hji; rw [hp] at hq; cases hq; exact hne
  · exact h j (by omega) q hq

theorem dk_kv_none {V : Type} (kv : List (List w8 × V)) (kb : List w8)
    (h : ∀ j < kv.length, ∀ q, kv[j]? = some q → q.1 ≠ kb) : ∀ q ∈ kv, q.1 ≠ kb := by
  intro q hq
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  exact h j hj _ (List.getElem?_eq_getElem hj)

theorem dk_kv_found {V : Type} (kv : List (List w8 × V)) (i : Nat) (p : List w8 × V) (kb : List w8)
    (hp : kv[i]? = some p) (heq : p.1 = kb) (h : ∀ j < i, ∀ q, kv[j]? = some q → q.1 ≠ kb) :
    (GMap.ofList kv).lookup kb = some p.2 := by
  subst heq
  exact ofList_lookup_first kv i p hp h

/-! ## The first index -/

/-- The first entry's index is the smallest key. -/
theorem first_min (I : DiskImg) (e : DEnt) (es : List DEnt) (h : I.ents = e :: es) (hok : IdxOk I.ents) :
    (I.logM.lookup (uint.nat e.idx)).isSome ∧ ∀ k x, I.logM.lookup k = some x → uint.nat e.idx ≤ k := by
  rw [logM_eq, h]
  refine ⟨?_, fun k x hx => ?_⟩
  · rw [ofList_isSome, entsB_keys]; exact List.mem_cons_self
  · have hs : ((GMap.ofList (entsB (e :: es))).lookup k).isSome := by rw [hx]; rfl
    rw [ofList_isSome, entsB_keys] at hs
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hs
    rw [h, idxOk_iff] at hok
    rcases List.mem_cons.1 hf with rfl | hf
    · exact Nat.le_refl _
    · exact Nat.le_of_lt ((List.pairwise_cons.1 hok.2).1 f hf)

theorem logM_empty (I : DiskImg) (h : I.ents = []) : I.logM = ∅ := by
  rw [logM_eq, h]; rfl

/-- `GetLog`'s loop: the entry at position `i` is the map's at its index. -/
theorem logM_lookup_at (I : DiskImg) (i : Nat) (e : DEnt) (h : I.ents[i]? = some e) (hok : IdxOk I.ents) :
    I.logM.lookup (uint.nat e.idx) = some (entOf e) := by
  rw [logM_eq]
  rw [idxOk_iff] at hok
  have := ofList_lookup_first (entsB I.ents) i (uint.nat e.idx, entOf e) (by simp [entsB, h])
    (fun j hj q hq => by
      simp only [entsB, List.getElem?_map, Option.map_eq_some_iff] at hq
      obtain ⟨f, hf, rfl⟩ := hq
      have := List.pairwise_iff_getElem.1 hok.2 j i (List.getElem?_eq_some_iff.1 hf).1
        (List.getElem?_eq_some_iff.1 h).1 hj
      simp only [(List.getElem?_eq_some_iff.1 hf).2, (List.getElem?_eq_some_iff.1 h).2] at this
      simp only; omega)
  exact this

/-- `GetLog`'s loop: no entry at that index. -/
theorem logM_lookup_none (I : DiskImg) (k : w64) (h : ∀ e ∈ I.ents, e.idx ≠ k) :
    I.logM.lookup (uint.nat k) = none := by
  rw [logM_eq]
  apply ofList_lookup_none'
  intro q hq
  simp only [entsB, List.mem_map] at hq
  obtain ⟨e, he, rfl⟩ := hq
  intro h'; exact h e he (by simp only at h'; word)

/-! ## Well-formedness from the encoding's length -/

/-- The structural part of `DiskImg.Ok` (the lengths follow from the encoding's, `ok_of_enc`). -/
def DiskImg.Pre (I : DiskImg) : Prop :=
  IdxOk I.ents ∧ (I.kv.map Prod.fst).Nodup ∧ (I.ikv.map Prod.fst).Nodup

theorem len_le_flatMap {α : Type} (l : List α) (f : α → List w8) (hf : ∀ x, 1 ≤ (f x).length) :
    l.length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := hf x; omega

theorem mem_le_flatMap {α : Type} (l : List α) (f : α → List w8) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := ih hx; omega

theorem ok_of_enc (I : DiskImg) (hp : I.Pre) (hl : (encImg I).length < 2 ^ 63) : I.Ok := by
  obtain ⟨h1, h2, h3⟩ := hp
  have he : (I.ents.flatMap encEnt).length + (I.kv.flatMap encKV).length + (I.ikv.flatMap encIKV).length ≤
      (encImg I).length := by
    simp only [encImg, List.length_append]; omega
  have hE : ∀ e, 1 ≤ (encEnt e).length := fun e => by simp [encEnt, encBytes, encU64_length]; omega
  have hK : ∀ p, 1 ≤ (encKV p).length := fun p => by simp [encKV, encBytes, encU64_length]; omega
  have hI : ∀ p, 1 ≤ (encIKV p).length := fun p => by simp [encIKV, encBytes, encU64_length]; omega
  refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · have := len_le_flatMap I.ents encEnt hE
    have := len_le_flatMap I.kv encKV hK
    have := len_le_flatMap I.ikv encIKV hI
    omega
  · intro e he'
    have := mem_le_flatMap I.ents encEnt e he'
    simp only [encEnt, encBytes, List.length_append] at this; omega
  · intro p hp'
    have := mem_le_flatMap I.kv encKV p hp'
    simp only [encKV, encBytes, List.length_append] at this; omega
  · intro p hp'
    have := mem_le_flatMap I.ikv encIKV p hp'
    simp only [encIKV, encBytes, List.length_append] at this; omega

theorem pre_of_ok (I : DiskImg) (h : I.Ok) : I.Pre := ⟨h.idx, h.kvKeys, h.ikvKeys⟩

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
