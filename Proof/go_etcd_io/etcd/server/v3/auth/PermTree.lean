/-
**The permission cache's trees against the model** (the auth plan's S2, 2026-10-23): the
interval `getMergedPerms` inserts for a permission (`permIvl`: the point `[key, key ++ "\x00")`,
the open range `[key, "")` for `"\x00"`, else `[key, rangeEnd)`), the intervals of a user's
permissions of a type (`ivlsOf`: what each of the entry's two trees holds), the interval
`checkKeyInterval` queries (`queryIvl`), and the bridge from the tree's pure meaning
(`adt.inIvl`, `adt.containsRes`, `Contains.lean`) to the model's `coversPoint`/`coversRange`
(`Model.lean`): a permission's interval holds a key exactly when the permission's range does
(`inIvl_permIvl`), for a permission with a non-empty key (`permKeysOk`: the affine order's top).
Nomode X-a3: the trees themselves (`treeOf`, `Model.lean`; `treeOf_ok`), the cache entry and its
verdict over them (`cacheEntryIs`, `cacheVerdictP`: Go's verdict `coversX`, for every request),
and the bridges to the coverage (`coversX_iff_covers`, `granted_iff_covers`, `coversX_emptyKey`,
`coversX_point_of_not_lt`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Model
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Contains
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Holes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open go_etcd_io.etcd.api.v3

section pure
variable [GooseExts]

/-- The model's operation type of the request side's `Permission_Type`: `READ` (`0`) is a read,
`WRITE` (`1`) a write (`permTypOk`). -/
def permOp (pt : authpb.Permission_Type) : PermType := if pt = W32 0 then .read else .write

theorem goStringLt_nil_of_ne {k : GoString} (hk : k ≠ []) : go.GoStringLt [] k := by
  cases k with
  | nil => exact absurd rfl hk
  | cons x xs => exact go.goStringLt_nil_cons x xs

/-- `k < key ++ "\x00"` is `k ≤ key`. -/
theorem goStringLt_succ_iff (k key : GoString) :
    go.GoStringLt k (key ++ [W8 0]) ↔ k = key ∨ go.GoStringLt k key := by
  constructor
  · intro h
    by_cases hlt : go.GoStringLt key k
    · rcases adt.strLt_succ_le hlt with heq | hlt'
      · exact absurd (heq ▸ h) (go.goStringLt_irrefl _)
      · exact absurd (go.goStringLt_trans h hlt') (go.goStringLt_irrefl _)
    · by_cases h2 : go.GoStringLt k key
      · exact Or.inr h2
      · exact Or.inl (go.goStringLt_eq_of_not_lt h2 hlt)
  · rintro (rfl | h)
    · exact adt.strLt_append k [W8 0] (by simp)
    · exact go.goStringLt_trans h (adt.strLt_append key [W8 0] (by simp))

/-- **A permission's interval holds a key exactly when its range does**, for a non-empty key
(the affine order's `""` is the top, the model's the least key). -/
theorem inIvl_permIvl (p : Perm) (hk : p.key ≠ []) (k : GoString) :
    adt.inIvl (permIvl p) k ↔ inRange p.key p.rangeEnd k := by
  unfold adt.inIvl permIvl inRange adt.affLt
  -- `k` at or above the key: not below it
  have hge : ∀ (hk' : k ≠ []), ¬ (k ≠ [] ∧ (p.key = [] ∨ go.GoStringLt k p.key)) ↔
      go.GoStringLe p.key k := by
    intro hk'
    unfold go.GoStringLe
    constructor
    · intro h1
      by_cases hlt : go.GoStringLt k p.key
      · exact absurd ⟨hk', Or.inr hlt⟩ h1
      · by_cases h3 : go.GoStringLt p.key k
        · exact Or.inr h3
        · exact Or.inl (go.goStringLt_eq_of_not_lt h3 hlt)
    · rintro h ⟨-, h2⟩
      rcases h2 with h2 | hlt
      · exact hk h2
      · rcases h with h | h
        · exact go.goStringLt_irrefl _ (h ▸ hlt)
        · exact go.goStringLt_irrefl _ (go.goStringLt_trans h hlt)
  have hkn : go.GoStringLe p.key k → k ≠ [] := by
    rintro h rfl
    rcases h with h | h
    · exact hk h
    · exact go.goStringLt_not_nil _ h
  by_cases he : p.rangeEnd = []
  · simp only [he, ↓reduceIte]
    have hne : p.key ++ [W8 0] ≠ [] := by simp
    constructor
    · rintro ⟨h1, hk', h2⟩
      rcases h2 with h2 | h2
      · exact absurd h2 hne
      · rcases (goStringLt_succ_iff k p.key).1 h2 with h2 | h2
        · exact h2
        · exact absurd ⟨hk', Or.inr h2⟩ h1
    · rintro rfl
      refine ⟨(hge hk).2 (Or.inl rfl), hk, Or.inr ?_⟩
      exact (goStringLt_succ_iff _ _).2 (Or.inl rfl)
  · by_cases ho : isOpenEnded p.rangeEnd
    · simp only [he, ho, ↓reduceIte]
      constructor
      · rintro ⟨h1, hk', -⟩
        refine ⟨(hge hk').1 h1, ?_⟩
        first | exact Or.inl ho | exact Or.inl trivial | trivial
      · rintro ⟨h, -⟩
        refine ⟨(hge (hkn h)).2 h, hkn h, ?_⟩
        first | exact Or.inl rfl | exact Or.inl trivial | trivial
    · simp only [he, ho, ↓reduceIte]
      constructor
      · rintro ⟨h1, hk', h2⟩
        rcases h2 with h2 | h2
        · first | exact h2.elim | exact absurd h2 he
        · exact ⟨(hge hk').1 h1, Or.inr h2⟩
      · rintro ⟨h, h2⟩
        rcases h2 with h2 | h2
        · first | exact h2.elim | exact absurd h2 ho
        · exact ⟨(hge (hkn h)).2 h, hkn h, Or.inr h2⟩

/-- The queried interval is the interval of a permission with that range (a non-empty one). -/
theorem queryIvl_eq_permIvl (key rangeEnd : GoString) (he : rangeEnd ≠ []) (ty : PermType) :
    queryIvl key rangeEnd = permIvl ⟨key, rangeEnd, ty⟩ := by
  unfold queryIvl permIvl
  by_cases ho : isOpenEnded rangeEnd <;> simp [he, ho]

/-- The queried interval holds a key exactly when the request's range does. -/
theorem inIvl_queryIvl (key rangeEnd : GoString) (hk : key ≠ []) (he : rangeEnd ≠ []) (k : GoString) :
    adt.inIvl (queryIvl key rangeEnd) k ↔ inRange key rangeEnd k := by
  rw [queryIvl_eq_permIvl key rangeEnd he .read]
  exact inIvl_permIvl ⟨key, rangeEnd, .read⟩ hk k

/-- The queried interval of a request with a non-empty key and an open-ended or proper range is
below its end (`Contains`' premise). -/
theorem queryIvl_ok (key rangeEnd : GoString) (hk : key ≠ [])
    (h : isOpenEnded rangeEnd ∨ go.GoStringLt key rangeEnd) :
    adt.affLt (queryIvl key rangeEnd).1 (queryIvl key rangeEnd).2 := by
  unfold queryIvl adt.affLt
  refine ⟨hk, ?_⟩
  by_cases ho : isOpenEnded rangeEnd
  · simp [ho]
  · simp only [ho, ↓reduceIte]
    rcases h with h | h
    · exact absurd h ho
    · exact Or.inr h

/-- A key is covered by a user's permissions of a type exactly when some interval of the
tree of that type holds it (a state whose permissions' keys are non-empty). -/
theorem covers_iff (st : AuthState) (u : User) (op : PermType) (k : GoString)
    (hst : permKeysOk st) :
    (∃ p ∈ userPerms st u, p.covers op k) ↔ ∃ x ∈ ivlsOf op (userPerms st u), adt.inIvl x k := by
  unfold ivlsOf Perm.covers
  constructor
  · rintro ⟨p, hp, hg, hr⟩
    obtain ⟨r, ps, hps, hpps⟩ := mem_userPerms hp
    refine ⟨permIvl p, List.mem_map_of_mem (List.mem_filter.2 ⟨hp, hg⟩), ?_⟩
    exact (inIvl_permIvl p (hst r ps hps p hpps) k).2 hr
  · rintro ⟨x, hx, hxk⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hp, hg⟩ := List.mem_filter.1 hp
    obtain ⟨r, ps, hps, hpps⟩ := mem_userPerms hp
    exact ⟨p, hp, hg, (inIvl_permIvl p (hst r ps hps p hpps) k).1 hxk⟩

/-- **`coversPoint` is the tree's point query** (`checkKeyPoint`). -/
theorem coversPoint_iff (st : AuthState) (u : User) (op : PermType) (key : GoString)
    (hst : permKeysOk st) :
    coversPoint st u op key ↔ ∃ x ∈ ivlsOf op (userPerms st u), adt.inIvl x key :=
  covers_iff st u op key hst

/-- **`coversRange` is the tree's coverage of the queried interval** (`checkKeyInterval`), for a
request with a non-empty key and a non-empty range. -/
theorem coversRange_iff (st : AuthState) (u : User) (op : PermType) (key rangeEnd : GoString)
    (hk : key ≠ []) (he : rangeEnd ≠ []) (hst : permKeysOk st) :
    coversRange st u op key rangeEnd ↔
      ∀ k, adt.inIvl (queryIvl key rangeEnd) k → ∃ x ∈ ivlsOf op (userPerms st u), adt.inIvl x k := by
  unfold coversRange
  constructor
  · intro H k hk'
    exact (covers_iff st u op k hst).1 (H k ((inIvl_queryIvl key rangeEnd hk he k).1 hk'))
  · intro H k hk'
    exact (covers_iff st u op k hst).2 (H k ((inIvl_queryIvl key rangeEnd hk he k).2 hk'))

/-- The intervals of a list of entries, as a multiset, determine what the entries hold. -/
theorem exists_inIvl_perm {L : List adt.Entry} {xs : List adt.IvlS}
    (h : (L.map Prod.fst).Perm xs) (k : GoString) :
    (∃ z ∈ L, adt.inIvl z.1 k) ↔ ∃ x ∈ xs, adt.inIvl x k := by
  constructor
  · rintro ⟨z, hz, hzk⟩
    exact ⟨z.1, h.mem_iff.1 (List.mem_map_of_mem hz), hzk⟩
  · rintro ⟨x, hx, hxk⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 (h.mem_iff.2 hx)
    exact ⟨z, hz, hxk⟩

/-! ## The trees `getMergedPerms` builds (nomode X-a3) -/

theorem perm_of_eq_aux {α : Type} {l₁ l₂ : List α} (h : l₁ = l₂) : l₁.Perm l₂ := by
  subst h; exact List.Perm.refl _

/-- Inserting the intervals `xs` in turn into a sorted tree: sorted, holding its entries and `xs`
(as multisets). -/
theorem foldl_insertRB_ok (v : GoInterface) : ∀ (xs : List adt.IvlS) (T : adt.RbT adt.Entry),
    adt.IvSorted T.inorder →
    adt.IvSorted (xs.foldl (fun T x => T.insertRB (x, v)) T).inorder ∧
      ((xs.foldl (fun T x => T.insertRB (x, v)) T).inorder.map Prod.fst).Perm
        (T.inorder.map Prod.fst ++ xs)
  | [], T, hs => ⟨hs, perm_of_eq_aux (by simp)⟩
  | x :: xs, T, hs => by
    have h1 := adt.RbT.inorder_insertRB (x, v) T hs
    have hs1 : adt.IvSorted (T.insertRB (x, v)).inorder := by
      rw [h1]; exact adt.ivtInsert_ivSorted _ _ hs
    obtain ⟨hA, hB⟩ := foldl_insertRB_ok v xs (T.insertRB (x, v)) hs1
    refine ⟨hA, hB.trans ?_⟩
    rw [h1]
    have h2 := (adt.ivtInsert_perm (x, v) T.inorder).map Prod.fst
    rw [List.map_cons] at h2
    have h3 : (x :: T.inorder.map Prod.fst).Perm (T.inorder.map Prod.fst ++ [x]) :=
      (List.perm_append_singleton x _).symm
    exact ((h2.trans h3).append_right xs).trans (perm_of_eq_aux (by simp))

/-- **`treeOf`'s entries**: sorted, and as multisets the intervals of the permissions (`ivlsOf`). -/
theorem treeOf_ok (op : PermType) (ps : List Perm) :
    adt.IvSorted (treeOf op ps).inorder ∧
      ((treeOf op ps).inorder.map Prod.fst).Perm (ivlsOf op ps) := by
  have h := foldl_insertRB_ok permVal (ivlsOf op ps) .leaf (by exact List.Pairwise.nil)
  unfold treeOf
  simpa using h

/-- One more permission: its interval inserted when it grants `op`. -/
theorem treeOf_snoc (op : PermType) (ps : List Perm) (p : Perm) :
    treeOf op (ps ++ [p]) =
      if p.ty.grants op then (treeOf op ps).insertRB (permIvl p, permVal) else treeOf op ps := by
  unfold treeOf ivlsOf
  rw [List.filter_append, List.map_append, List.foldl_append]
  by_cases h : p.ty.grants op = true
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

theorem treeOf_nil (op : PermType) : treeOf op [] = .leaf := rfl

/-- **The cache entry of the user `u` at `st`** (`getMergedPerms`): the user exists, and the
entry's trees are those `getMergedPerms` builds from the user's permissions (`treeOf`): the read
tree from those granting reads, the write tree from those granting writes. -/
def cacheEntryIs (st : AuthState) (u : GoString) (Tr Tw : adt.RbT adt.Entry) : Prop :=
  ∃ roles, st.users !! u = some roles ∧
    Tr = treeOf .read (userPerms st roles) ∧ Tw = treeOf .write (userPerms st roles)

/-- **`isRangeOpPermitted`'s verdict at the cache's state `sc`** (pure; every request): the check
passes exactly when the user exists at `sc` and Go's verdict on the request over its permissions
holds (`coversX`). -/
def cacheVerdictP (sc : AuthState) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) : Prop :=
  b = true ↔ ∃ roles, sc.users !! user = some roles ∧ coversX sc roles (permOp pt) k e = true

open Classical in
/-- `coversX` of a point: some interval of the permissions holds the key. -/
theorem coversX_point (st : AuthState) (u : User) (op : PermType) (k : GoString) :
    coversX st u op k [] = true ↔ ∃ x ∈ ivlsOf op (userPerms st u), adt.inIvl x k := by
  unfold coversX
  rw [if_pos rfl]
  exact decide_eq_true_iff

/-- **The check's answer on the entry's trees is `coversX`**: the point query
(`checkKeyPoint`: some entry of the tree of the type holds the key) or `Contains` of the queried
interval on that tree (`checkKeyInterval`), the trees `getMergedPerms` built. -/
theorem coversX_entry (sc : AuthState) (roles : User)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (k e : GoString) (b : Bool)
    (Tr Tw : adt.RbT adt.Entry) (hpt : pt = W32 0 ∨ pt = W32 1)
    (hTr : Tr = treeOf .read (userPerms sc roles)) (hTw : Tw = treeOf .write (userPerms sc roles))
    (hb : (e = [] → (b = true ↔ ∃ z ∈ (if pt = W32 0 then Tr else Tw).inorder, adt.inIvl z.1 k)) ∧
      (e ≠ [] → b = adt.containsT (queryIvl k e) (if pt = W32 0 then Tr else Tw))) :
    b = coversX sc roles (permOp pt) k e := by
  have hT : (if pt = W32 0 then Tr else Tw) = treeOf (permOp pt) (userPerms sc roles) := by
    unfold permOp
    rcases hpt with rfl | rfl
    · simp only [↓reduceIte]; exact hTr
    · have h10 : ¬ ((W32 1 : w32) = W32 0) := by decide
      rw [if_neg h10, if_neg h10]; exact hTw
  rw [hT] at hb
  by_cases he : e = []
  · subst he
    have h1 := hb.1 rfl
    have h2 := exists_inIvl_perm (treeOf_ok (permOp pt) (userPerms sc roles)).2 k
    apply Bool.eq_iff_iff.2
    rw [h1, h2, coversX_point]
  · unfold coversX
    rw [if_neg he]
    exact hb.2 he

/-- **The cache's verdict from its entry**: `cacheVerdictP` of the entry's state. -/
theorem cacheVerdictP_entry (sc : AuthState) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type) (b : Bool) (Tr Tw : adt.RbT adt.Entry)
    (hpt : pt = W32 0 ∨ pt = W32 1) (Hent : cacheEntryIs sc user Tr Tw)
    (hb : (e = [] → (b = true ↔ ∃ z ∈ (if pt = W32 0 then Tr else Tw).inorder, adt.inIvl z.1 k)) ∧
      (e ≠ [] → b = adt.containsT (queryIvl k e) (if pt = W32 0 then Tr else Tw))) :
    cacheVerdictP sc user k e pt b := by
  obtain ⟨roles, hroles, hTr, hTw⟩ := Hent
  have hbx := coversX_entry sc roles pt k e b Tr Tw hpt hTr hTw hb
  subst hbx
  unfold cacheVerdictP
  constructor
  · intro h; exact ⟨roles, hroles, h⟩
  · rintro ⟨roles', hr', h⟩
    rw [hroles] at hr'; cases hr'; exact h

/-- No entry for the user, the cache's keys the state's users: a refusal. -/
theorem cacheVerdictP_absent (sc : AuthState) (Mp : GMap GoString Loc) (user k e : GoString)
    (pt : go_etcd_io.etcd.api.v3.authpb.Permission_Type)
    (hdom : ∀ u, (Mp !! u).isSome ↔ (sc.users !! u).isSome) (h : Mp !! user = none) :
    cacheVerdictP sc user k e pt false := by
  have hu : sc.users !! user = none := by
    have hd := hdom user
    rw [h] at hd
    cases hs : sc.users !! user with
    | none => rfl
    | some r => rw [hs] at hd; simp at hd
  unfold cacheVerdictP
  simp only [hu, Bool.false_eq_true, false_iff, not_exists, not_and]
  intro _ hr; cases hr

/-! ## Bridges to the coverage (`covers`) -/

/-- `coversX` of a range of the shape the cache decides (a non-empty key, open-ended or proper):
the coverage of the queried interval by the permissions' intervals. -/
theorem coversX_range (st : AuthState) (u : User) (op : PermType) (k e : GoString) (he : e ≠ [])
    (hk : k ≠ []) (hs : isOpenEnded e ∨ go.GoStringLt k e) :
    coversX st u op k e = true ↔
      ∀ x, adt.inIvl (queryIvl k e) x → ∃ y ∈ ivlsOf op (userPerms st u), adt.inIvl y x := by
  unfold coversX
  rw [if_neg he]
  obtain ⟨hsort, hperm⟩ := treeOf_ok op (userPerms st u)
  have hq := queryIvl_ok k e hk hs
  rw [adt.containsT_eq _ _ hsort (Or.inr hq), adt.containsRes_iff _ _ hsort hq]
  exact forall_congr' fun x => imp_congr_right fun _ => exists_inIvl_perm hperm x

/-- **Go's verdict is the coverage on the shape the cache decides** (`reqShape`), in a state whose
permissions' keys are non-empty (`permKeysOk`). -/
theorem coversX_iff_covers (st : AuthState) (u : User) (op : PermType) (k e : GoString)
    (hkeys : permKeysOk st) (hs : reqShape k e) :
    coversX st u op k e = true ↔ covers st u op k e := by
  unfold covers
  by_cases he : e = []
  · rw [if_pos he]
    subst he
    rw [coversX_point, coversPoint_iff st u op k hkeys]
  · rw [if_neg he, coversRange_iff st u op k e hs.1 he hkeys]
    exact coversX_range st u op k e he hs.1 (hs.2.resolve_left he)

/-- **`granted` in its coverage form** on the shape the cache decides (`reqShape`) and non-empty
permission keys: the form the request side's proofs not yet on `coversX` use. -/
theorem granted_iff_covers (st : AuthState) (ai : AuthInfoM) (k e : GoString) (op : PermType)
    (hkeys : permKeysOk st) (hs : reqShape k e) :
    granted st ai k e op ↔ ai.rev ≠ 0 ∧ ∃ u, st.users !! ai.user = some u ∧
      (isRoot u ∨ (reqShape k e → covers st u op k e)) := by
  unfold granted
  constructor
  · rintro ⟨h0, u, hu, hr | hc⟩
    · exact ⟨h0, u, hu, Or.inl hr⟩
    · exact ⟨h0, u, hu, Or.inr fun _ => (coversX_iff_covers st u op k e hkeys hs).1 hc⟩
  · rintro ⟨h0, u, hu, hr | hc⟩
    · exact ⟨h0, u, hu, Or.inl hr⟩
    · exact ⟨h0, u, hu, Or.inr ((coversX_iff_covers st u op k e hkeys hs).2 (hc hs))⟩

open Classical in
/-- **An empty key is refused** (every range end): the point `[k, k ++ "\x00")` of `""` holds no
key, and `Visit` of a query whose begin is the top `""` visits nothing. -/
theorem coversX_emptyKey (st : AuthState) (u : User) (op : PermType) (e : GoString) :
    coversX st u op [] e = false := by
  unfold coversX
  by_cases he : e = []
  · rw [if_pos he]
    apply decide_eq_false
    rintro ⟨x, -, -, h⟩
    exact adt.not_affLt_empty _ h
  · rw [if_neg he]
    obtain ⟨hsort, -⟩ := treeOf_ok op (userPerms st u)
    have hq1 : (queryIvl [] e).1 = go!"" := rfl
    have hstab : adt.stab (queryIvl [] e) (treeOf op (userPerms st u)).inorder = [] :=
      (adt.stab_eq_nil_iff _ _).2 fun z _ => adt.no_ovl_of_end_le (adt.not_affLt_empty _)
    rw [adt.containsT_eq _ _ hsort (Or.inl hq1)]
    simp only [adt.containsRes, hstab]

/-- `Contains` true of a query whose end is not above its begin (an empty or inverted range): an
entry holds the query's begin (every entry `Visit` hands the scan overlaps the query, `ivlCmp`). -/
theorem containsT_true_holds (q : adt.IvlS) (T : adt.RbT adt.Entry) (hq : ¬ adt.affLt q.1 q.2)
    (h : adt.containsT q T = true) : ∃ z ∈ T.inorder, adt.inIvl z.1 q.1 := by
  unfold adt.containsT at h
  cases hv : T.visitL q with
  | nil => simp only [hv, Bool.false_eq_true] at h
  | cons z zs =>
    have hz : z ∈ adt.stab q T.inorder :=
      (adt.visitL_sublist q T).subset (by rw [hv]; exact List.mem_cons_self)
    obtain ⟨hzT, hc⟩ := (adt.mem_stab _ _ _).1 hz
    rw [adt.ivlCmp_eq_zero_iff] at hc
    exact ⟨z, hzT, fun hlt => hq (adt.affLt_trans hlt (hc.1 hlt)), hc.2⟩

/-- **An empty (`[k, k)`) or inverted range granted is the point `k` covered** (in a state with
non-empty permission keys): `Contains` passes only through an interval holding the begin. (The
converse for `[k, k)` holds of permissions with valid ranges, `rangeValid`, which `permKeysOk` does
not state.) -/
theorem coversX_point_of_not_lt (st : AuthState) (u : User) (op : PermType) (k e : GoString)
    (hkeys : permKeysOk st) (he : e ≠ []) (hno : ¬ isOpenEnded e) (hle : ¬ go.GoStringLt k e)
    (h : coversX st u op k e = true) : coversPoint st u op k := by
  unfold coversX at h
  rw [if_neg he] at h
  have hq : queryIvl k e = (k, e) := by unfold queryIvl; simp [hno]
  have hnaff : ¬ adt.affLt (queryIvl k e).1 (queryIvl k e).2 := by
    rw [hq]
    rintro ⟨-, h1 | h1⟩
    · exact he h1
    · exact hle h1
  obtain ⟨z, hz, hin⟩ := containsT_true_holds _ _ hnaff h
  rw [coversPoint_iff st u op k hkeys]
  exact (exists_inIvl_perm (treeOf_ok op (userPerms st u)).2 k).1 ⟨z, hz, hin⟩

end pure

end auth
end EtcdGrove
end Perennial
