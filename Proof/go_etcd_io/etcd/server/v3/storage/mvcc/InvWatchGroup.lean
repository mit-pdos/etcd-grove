/-
The watcher group (`watcher_group.go`): a set of watcher pointers, indexed by key (the
single-key watchers, `keyWatchers`) and by interval (the range watchers, in the interval tree
`ranges`, through its contract `adt.ownIvt`), with the set of all members (`watchers`).
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The watcher group and the stream
(unit 2)".

**Representation.** A watcher's range (`key`, `end`) and `startRev`, `id`, `fcs` are written
by `watch()` only, before the watcher is shared: a persistent fact of its pointer
(`watcherFixed w r fcs`, as a key index's `kiKey`). `ownWatcherGroup wg W` holds the group at
`wg` with the members `W` (pointer ↦ range): the all-watchers set holds `dom W`; the key map
has one non-empty set per key of a single-key member (`keyMembers W k`); the tree has one
entry per distinct interval of the range members, in the tree's order, its value the set
(`ivlMembers W ivl`) as an interface value of the named map type `watcherSet`. The members'
mutable fields (`minRev`, `victim`, `compacted`, `restore`, `ch`: `watcherOwn`) are not the
group's: the store's, or the batch's (unit 2a2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## Ranges and members (pure) -/

/-- A watcher's fixed range: a single key (`end == nil`, `end? = none`), or `[key, end)` under
the affine order (`end` empty, non-nil, is +∞: a `WithFromKey` watch); and its `startRev` and
`id`, fixed too. -/
structure WatchRange where
  key : GoString
  end? : Option GoString
  startRev : w64
  id : w64

/-- The key `k` is in the range. -/
def WatchRange.covers (r : WatchRange) (k : GoString) : Bool :=
  match r.end? with
  | none => decide (k = r.key)
  | some e => decide (adt.affCmp k r.key ≥ 0 ∧ adt.affCmp k e < 0)

/-- The range watcher's interval in the tree. -/
def WatchRange.ivl (r : WatchRange) (e : GoString) : adt.IvlS := (r.key, e)

/-- The members (of `W`) whose range satisfies `p`, as a set. -/
def membersBy (W : GMap Loc WatchRange) (p : WatchRange → Bool) : GMap Loc Unit :=
  GMap.fmap (fun _ => ()) (GMap.filter (fun _ r => p r) W)

/-- The single-key members of the key `k`. -/
def keyMembers (W : GMap Loc WatchRange) (k : GoString) : GMap Loc Unit :=
  membersBy W fun r => r.end? = none && decide (r.key = k)

/-- The range members of the interval `ivl`. -/
def ivlMembers (W : GMap Loc WatchRange) (ivl : adt.IvlS) : GMap Loc Unit :=
  membersBy W fun r => decide (r.end?.map (fun e => (r.key, e)) = some ivl)

theorem membersBy_lookup (W : GMap Loc WatchRange) (p : WatchRange → Bool) (w : Loc) :
    membersBy W p !! w = (match W !! w with
      | some r => if p r then some () else none
      | none => none) := by
  unfold membersBy
  simp only [GMap.lookup_fmap, GMap.lookup_filter]
  cases W !! w with
  | none => rfl
  | some r => by_cases h : p r <;> simp [h]

theorem mem_membersBy (W : GMap Loc WatchRange) (p : WatchRange → Bool) (w : Loc) :
    (membersBy W p !! w).isSome ↔ ∃ r, W !! w = some r ∧ p r = true := by
  rw [membersBy_lookup]
  cases h : W !! w with
  | none => simp
  | some r => by_cases hp : p r <;> simp [hp]

theorem membersBy_insert (W : GMap Loc WatchRange) (p : WatchRange → Bool) (w : Loc)
    (r : WatchRange) :
    membersBy (<[w := r]> W) p =
      if p r then <[w := ()]> (membersBy W p) else GMap.delete w (membersBy W p) := by
  refine GMap.ext (fun k => ?_)
  by_cases hk : k = w
  · subst hk
    rw [membersBy_lookup, GMap.lookup_insert]
    by_cases hp : p r <;> simp [hp]
  · rw [membersBy_lookup, GMap.lookup_insert_ne _ _ (Ne.symm hk)]
    by_cases hp : p r <;>
      simp only [hp, ite_true, ite_false, Bool.false_eq_true, GMap.lookup_insert_ne _ _ (Ne.symm hk),
        GMap.lookup_delete_ne _ (Ne.symm hk), membersBy_lookup]

theorem membersBy_insert_none (W : GMap Loc WatchRange) (p : WatchRange → Bool) (w : Loc)
    (r : WatchRange) (hw : W !! w = none) :
    membersBy (<[w := r]> W) p = if p r then <[w := ()]> (membersBy W p) else membersBy W p := by
  rw [membersBy_insert]
  split
  · rfl
  · apply GMap.delete_notin
    rw [membersBy_lookup, hw]

theorem membersBy_delete (W : GMap Loc WatchRange) (p : WatchRange → Bool) (w : Loc) :
    membersBy (GMap.delete w W) p = GMap.delete w (membersBy W p) := by
  refine GMap.ext (fun k => ?_)
  by_cases hk : k = w
  · subst hk
    rw [membersBy_lookup, GMap.lookup_delete, GMap.lookup_delete]
  · rw [membersBy_lookup, GMap.lookup_delete_ne _ (Ne.symm hk),
      GMap.lookup_delete_ne _ (Ne.symm hk), membersBy_lookup]

theorem membersBy_empty_iff (W : GMap Loc WatchRange) (p : WatchRange → Bool) :
    membersBy W p = ∅ ↔ ¬ ∃ w r, W !! w = some r ∧ p r = true := by
  rw [GMap.mapEmpty]
  constructor
  · rintro h ⟨w, r, hw, hp⟩
    have := (mem_membersBy W p w).2 ⟨r, hw, hp⟩
    rw [h w] at this; cases this
  · intro h w
    cases hm : membersBy W p !! w with
    | none => rfl
    | some _ =>
      exfalso; apply h
      obtain ⟨r, hr, hp⟩ := (mem_membersBy W p w).1 (by rw [hm]; rfl)
      exact ⟨w, r, hr, hp⟩

theorem keyMembers_insert_ne (W : GMap Loc WatchRange) (wa : Loc) (r : WatchRange)
    (k : GoString) (hw : W !! wa = none) (h : ¬ (r.end? = none ∧ r.key = k)) :
    keyMembers (<[wa := r]> W) k = keyMembers W k := by
  unfold keyMembers
  rw [membersBy_insert_none _ _ _ _ hw]
  have : (r.end? = none && decide (r.key = k)) = false := by
    cases he : r.end? <;> simp_all
  rw [this]; rfl

theorem keyMembers_insert_eq (W : GMap Loc WatchRange) (wa : Loc) (r : WatchRange)
    (hw : W !! wa = none) (h : r.end? = none) :
    keyMembers (<[wa := r]> W) r.key = <[wa := ()]> (keyMembers W r.key) := by
  unfold keyMembers
  rw [membersBy_insert_none _ _ _ _ hw]
  have : (r.end? = none && decide (r.key = r.key)) = true := by simp [h]
  rw [this]; rfl

theorem keyMembers_delete (W : GMap Loc WatchRange) (wa : Loc) (k : GoString) :
    keyMembers (GMap.delete wa W) k = GMap.delete wa (keyMembers W k) :=
  membersBy_delete _ _ _

theorem keyMembers_empty_iff (W : GMap Loc WatchRange) (k : GoString) :
    keyMembers W k = ∅ ↔ ¬ ∃ w r, W !! w = some r ∧ r.end? = none ∧ r.key = k := by
  unfold keyMembers
  rw [membersBy_empty_iff]
  simp

theorem ivlMembers_insert_ne (W : GMap Loc WatchRange) (wa : Loc) (r : WatchRange)
    (ivl : adt.IvlS) (hw : W !! wa = none) (h : r.end?.map (fun e => (r.key, e)) ≠ some ivl) :
    ivlMembers (<[wa := r]> W) ivl = ivlMembers W ivl := by
  unfold ivlMembers
  rw [membersBy_insert_none _ _ _ _ hw]
  simp [h]

theorem ivlMembers_insert_eq (W : GMap Loc WatchRange) (wa : Loc) (r : WatchRange)
    (e : GoString) (hw : W !! wa = none) (h : r.end? = some e) :
    ivlMembers (<[wa := r]> W) (r.key, e) = <[wa := ()]> (ivlMembers W (r.key, e)) := by
  unfold ivlMembers
  rw [membersBy_insert_none _ _ _ _ hw]
  simp [h]

theorem ivlMembers_delete (W : GMap Loc WatchRange) (wa : Loc) (ivl : adt.IvlS) :
    ivlMembers (GMap.delete wa W) ivl = GMap.delete wa (ivlMembers W ivl) :=
  membersBy_delete _ _ _

theorem ivlMembers_empty_iff (W : GMap Loc WatchRange) (ivl : adt.IvlS) :
    ivlMembers W ivl = ∅ ↔ ¬ ∃ w r e, W !! w = some r ∧ r.end? = some e ∧ ivl = (r.key, e) := by
  unfold ivlMembers
  rw [membersBy_empty_iff]
  constructor
  · rintro h ⟨w, r, e, hw, he, rfl⟩
    exact h ⟨w, r, hw, by simp [he]⟩
  · rintro h ⟨w, r, hw, hp⟩
    apply h
    cases he : r.end? with
    | none => simp [he] at hp
    | some e => simp [he] at hp; exact ⟨w, r, e, hw, he, hp.symm⟩

/-! ## The point interval of a key -/

section pure
open adt

/-- `k ++ "\x00"` is the immediate successor of `k`: a string above `k` is at least it. -/
theorem strLt_succ_le {k b : GoString} (h : go.GoStringLt k b) :
    k ++ go!"\x00" = b ∨ go.GoStringLt (k ++ go!"\x00") b := by
  induction k generalizing b with
  | nil =>
    cases h with
    | nil =>
      rename_i c bs
      by_cases hc : c = W8 0
      · subst hc
        cases bs with
        | nil => exact Or.inl rfl
        | cons d ds => exact Or.inr (List.Lex.cons List.Lex.nil)
      · right
        show List.Lex _ [W8 0] (c :: bs)
        apply List.Lex.rel
        have : uint.Z c ≠ 0 := by
          intro h0; apply hc; apply BitVec.eq_of_toNat_eq
          simp only [uint.Z] at h0; simp; omega
        have h1 : 0 ≤ uint.Z c := by simp [uint.Z]
        have h2 : uint.Z (W8 0) = 0 := by decide
        omega
  | cons x xs ih =>
    cases h with
    | cons h =>
      rcases ih h with e | h'
      · exact Or.inl (by rw [List.cons_append, e])
      · exact Or.inr (List.Lex.cons h')
    | rel h => exact Or.inr (List.Lex.rel h)

theorem succ_ne_empty (k : GoString) : k ++ go!"\x00" ≠ go!"" := by
  intro h; have := congrArg List.length h; simp at this

/-- The point interval of a key overlaps `[b, e)` exactly when the key is in it. -/
theorem ivlCmp_point_iff (k b e : GoString) :
    adt.ivlCmp (k, k ++ go!"\x00") (b, e) = 0 ↔ adt.affCmp k b ≥ 0 ∧ adt.affCmp k e < 0 := by
  have hb := affCmp_bounds k b
  have he := affCmp_bounds k e
  have hsucc : affCmp k b < 0 → affCmp (k ++ go!"\x00") b ≤ 0 := by
    intro hkb
    obtain ⟨hk, hb'⟩ := (affCmp_neg_iff k b).1 hkb
    rcases hb' with rfl | hlt
    · have := (affCmp_neg_iff (k ++ go!"\x00") go!"").2 ⟨succ_ne_empty k, Or.inl rfl⟩
      omega
    · rcases strLt_succ_le hlt with heq | hlt'
      · rw [heq, affCmp_self]; omega
      · have hbne : b ≠ go!"" := by
          rintro rfl; cases hlt
        have := (affCmp_neg_iff (k ++ go!"\x00") b).2 ⟨succ_ne_empty k, Or.inr hlt'⟩
        omega
  unfold ivlCmp
  simp only
  split
  · rename_i h; have := h.1; omega
  · rename_i h
    have h1 : ¬ affCmp k b < 0 := fun h1 => h ⟨h1, hsucc h1⟩
    split <;> omega

/-- Erasing the entry of an interval from distinct entries. -/
theorem mem_eraseP_fst {α : Type} (L : List (adt.IvlS × α)) (hnd : (L.map Prod.fst).Nodup)
    (ivl : adt.IvlS) (z : adt.IvlS × α) :
    z ∈ L.eraseP (fun z => decide (z.1 = ivl)) ↔ z ∈ L ∧ z.1 ≠ ivl := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases hy : y.1 = ivl
    · rw [List.eraseP_cons_of_pos (by simpa using hy)]
      constructor
      · intro hz
        refine ⟨List.mem_cons_of_mem _ hz, ?_⟩
        rintro rfl
        exact hnd.1 (hy ▸ List.mem_map_of_mem hz)
      · rintro ⟨hz, hne⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact absurd hy hne
        · exact hz
    · rw [List.eraseP_cons_of_neg (by simpa using hy)]
      rw [List.mem_cons, List.mem_cons, ih hnd.2]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hy⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩

theorem sorted_nodup {α : Type} (L : List (adt.IvlS × α))
    (hs : L.Pairwise (fun a b => adt.ivlLt a.1 b.1)) : (L.map Prod.fst).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact hs.imp (fun {a b} h (e : a.1 = b.1) => adt.ivlLt_irrefl b.1 (e ▸ h))

end pure

/-! ## The ranges holding a key -/

section ranges
variable [ext : FfiSyntax]

theorem covers_none (r : WatchRange) (k : GoString) (h : r.end? = none) :
    r.covers k = true ↔ k = r.key := by
  unfold WatchRange.covers; rw [h]; simp

theorem covers_some (r : WatchRange) (k e : GoString) (h : r.end? = some e) :
    r.covers k = true ↔ adt.ivlCmp (k, k ++ go!"\x00") (r.key, e) = 0 := by
  unfold WatchRange.covers; rw [h, ivlCmp_point_iff]; simp

/-- The tree's entries a key's point interval overlaps are those of the range members
holding the key. -/
theorem stab_point_ne_nil_iff (W : GMap Loc WatchRange) (L : List adt.Entry)
    (hL : ∀ ivl, ivl ∈ L.map Prod.fst ↔
      ∃ w r e, W !! w = some r ∧ r.end? = some e ∧ ivl = (r.key, e))
    (k : GoString) :
    adt.stab (k, k ++ go!"\x00") L ≠ [] ↔
      ∃ w r e, W !! w = some r ∧ r.end? = some e ∧ r.covers k = true := by
  unfold adt.stab
  rw [Ne, List.filter_eq_nil_iff]
  simp only [decide_eq_true_eq, Classical.not_forall, Classical.not_not]
  constructor
  · rintro ⟨z, hz, hc⟩
    obtain ⟨w, r, e, hw, he, hzr⟩ := (hL z.1).1 (List.mem_map_of_mem hz)
    exact ⟨w, r, e, hw, he, (covers_some r k e he).2 (hzr ▸ hc)⟩
  · rintro ⟨w, r, e, hw, he, hc⟩
    obtain ⟨z, hz, hzr⟩ := List.mem_map.1 ((hL (r.key, e)).2 ⟨w, r, e, hw, he, rfl⟩)
    exact ⟨z, hz, hzr ▸ (covers_some r k e he).1 hc⟩

end ranges

/-! ## The tree's entries under a change of members -/

section rangesOk
variable [ext : FfiSyntax]

/-- The entries `L` of the interval tree of the members `W`: in the tree's order, one per
distinct interval of the range members, each with its set. -/
def RangesOk (W : GMap Loc WatchRange) (L : List adt.Entry) : Prop :=
  L.Pairwise (fun a b => adt.ivlLt a.1 b.1) ∧
  ∀ ivl, ivl ∈ L.map Prod.fst ↔ ∃ w r e, W !! w = some r ∧ r.end? = some e ∧ ivl = (r.key, e)

/-- Two entries at different indices of distinct entries have different intervals. -/
theorem entries_ne {α : Type} (L : List (adt.IvlS × α)) (hnd : (L.map Prod.fst).Nodup)
    {i k : Nat} {y z : adt.IvlS × α} (hy : L[k]? = some y) (hz : L[i]? = some z) (hki : k ≠ i) :
    y.1 ≠ z.1 := by
  intro h
  have hy' : (L.map Prod.fst)[k]? = some z.1 := by rw [List.getElem?_map, hy]; simp [h]
  have hz' : (L.map Prod.fst)[i]? = some z.1 := by rw [List.getElem?_map, hz]; rfl
  exact hki (list_nodup_getElem?_inj _ hnd k i z.1 hy' hz')

/-- Adding a single-key member leaves the tree's entries as they are. -/
theorem rangesOk_insert_key (W : GMap Loc WatchRange) (L : List adt.Entry) (wa : Loc)
    (r : WatchRange) (hw : W !! wa = none) (he : r.end? = none) (hL : RangesOk W L) :
    RangesOk (<[wa := r]> W) L := by
  refine ⟨hL.1, fun ivl => ?_⟩
  rw [hL.2 ivl]
  constructor
  · rintro ⟨w, r', e, hw', he', rfl⟩
    refine ⟨w, r', e, ?_, he', rfl⟩
    rw [GMap.lookup_insert_ne _ _ (fun h => by subst h; rw [hw] at hw'; cases hw')]
    exact hw'
  · rintro ⟨w, r', e, hw', he', rfl⟩
    by_cases hww : w = wa
    · subst hww; rw [GMap.lookup_insert] at hw'; cases hw'; rw [he] at he'; cases he'
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hww)] at hw'
      exact ⟨w, r', e, hw', he', rfl⟩

/-- Adding a range member whose interval the tree has (`L`), or gets (`L'`). -/
theorem rangesOk_insert_range (W : GMap Loc WatchRange) (L L' : List adt.Entry) (wa : Loc)
    (r : WatchRange) (e : GoString) (hw : W !! wa = none) (he : r.end? = some e)
    (hL : ∀ ivl, ivl ∈ L.map Prod.fst ↔
      ∃ w r e, W !! w = some r ∧ r.end? = some e ∧ ivl = (r.key, e))
    (hs : L'.Pairwise (fun a b => adt.ivlLt a.1 b.1))
    (hL' : ∀ ivl, ivl ∈ L'.map Prod.fst ↔ ivl ∈ L.map Prod.fst ∨ ivl = (r.key, e)) :
    RangesOk (<[wa := r]> W) L' := by
  refine ⟨hs, fun ivl => ?_⟩
  rw [hL', hL ivl]
  constructor
  · rintro (⟨w, r', e', hw', he', rfl⟩ | rfl)
    · refine ⟨w, r', e', ?_, he', rfl⟩
      rw [GMap.lookup_insert_ne _ _ (fun h => by subst h; rw [hw] at hw'; cases hw')]
      exact hw'
    · exact ⟨wa, r, e, GMap.lookup_insert _ _ _, he, rfl⟩
  · rintro ⟨w, r', e', hw', he', rfl⟩
    by_cases hww : w = wa
    · subst hww; rw [GMap.lookup_insert] at hw'; cases hw'; rw [he] at he'; cases he'
      exact Or.inr rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hww)] at hw'
      exact Or.inl ⟨w, r', e', hw', he', rfl⟩

/-- Removing a member changes the members of no interval but its own. -/
theorem exists_ivl_delete (W : GMap Loc WatchRange) (wa : Loc) (r : WatchRange)
    (hw : W !! wa = some r) (ivl : adt.IvlS)
    (hne : r.end?.map (fun e => (r.key, e)) ≠ some ivl) :
    (∃ w r' e, GMap.delete wa W !! w = some r' ∧ r'.end? = some e ∧ ivl = (r'.key, e)) ↔
      ∃ w r' e, W !! w = some r' ∧ r'.end? = some e ∧ ivl = (r'.key, e) := by
  constructor
  · rintro ⟨w, r', e, hw', he', rfl⟩
    by_cases hww : w = wa
    · subst hww; rw [GMap.lookup_delete] at hw'; cases hw'
    · rw [GMap.lookup_delete_ne _ (Ne.symm hww)] at hw'; exact ⟨w, r', e, hw', he', rfl⟩
  · rintro ⟨w, r', e, hw', he', rfl⟩
    by_cases hww : w = wa
    · subst hww; rw [hw] at hw'; cases hw'; rw [he'] at hne; exact absurd rfl hne
    · rw [← GMap.lookup_delete_ne _ (Ne.symm hww)] at hw'; exact ⟨w, r', e, hw', he', rfl⟩

/-- The interval sets of an interval `wa`'s range is not. -/
theorem ivlMembers_delete_ne (W : GMap Loc WatchRange) (wa : Loc) (r : WatchRange)
    (hw : W !! wa = some r) (ivl : adt.IvlS)
    (hne : r.end?.map (fun e => (r.key, e)) ≠ some ivl) :
    ivlMembers (GMap.delete wa W) ivl = ivlMembers W ivl := by
  rw [ivlMembers_delete]
  apply GMap.delete_notin
  rw [ivlMembers, membersBy_lookup, hw]
  simp [hne]

/-- Removing a single-key member leaves the tree's entries as they are. -/
theorem rangesOk_delete_key (W : GMap Loc WatchRange) (L : List adt.Entry) (wa : Loc)
    (r : WatchRange) (hw : W !! wa = some r) (he : r.end? = none) (hL : RangesOk W L) :
    RangesOk (GMap.delete wa W) L :=
  ⟨hL.1, fun ivl => by rw [hL.2 ivl, exists_ivl_delete W wa r hw ivl (by rw [he]; simp)]⟩

/-- The first entry satisfying `p` and the others. -/
theorem perm_eraseP_of_find? {α : Type} (L : List α) (p : α → Bool) (z : α)
    (h : L.find? p = some z) : L.Perm (z :: L.eraseP p) := by
  induction L with
  | nil => cases h
  | cons y ys ih =>
    by_cases hy : p y = true
    · rw [List.find?_cons_of_pos hy] at h
      cases h
      rw [List.eraseP_cons_of_pos hy]
    · rw [List.find?_cons_of_neg (by simpa using hy)] at h
      rw [List.eraseP_cons_of_neg (by simpa using hy)]
      exact (List.Perm.cons y (ih h)).trans (List.Perm.swap z y _)

/-- The members of the key `key` or of one of the intervals `ivls` (a prefix of the ones
`watcherSetByKey` unions). -/
def coverUpTo (W : GMap Loc WatchRange) (key : GoString) (ivls : List adt.IvlS) :
    GMap Loc Unit :=
  membersBy W fun r => (r.end? = none && decide (r.key = key)) ||
    decide (r.end?.map (fun e => (r.key, e)) ∈ ivls.map some)

theorem coverUpTo_nil (W : GMap Loc WatchRange) (key : GoString) :
    coverUpTo W key [] = keyMembers W key := by
  unfold coverUpTo keyMembers
  congr 1; funext r; simp

theorem membersBy_or (W : GMap Loc WatchRange) (p q : WatchRange → Bool) :
    membersBy W (fun r => p r || q r) = membersBy W p ∪ membersBy W q := by
  refine GMap.ext (fun w => ?_)
  rw [GMap.lookup_union, membersBy_lookup, membersBy_lookup, membersBy_lookup]
  cases W !! w with
  | none => rfl
  | some r => cases hp : p r <;> cases hq : q r <;> simp [hp, hq]

theorem coverUpTo_snoc (W : GMap Loc WatchRange) (key : GoString) (ivls : List adt.IvlS)
    (ivl : adt.IvlS) :
    coverUpTo W key (ivls ++ [ivl]) = coverUpTo W key ivls ∪ ivlMembers W ivl := by
  unfold coverUpTo ivlMembers
  rw [← membersBy_or]
  congr 1
  funext r
  rw [Bool.or_assoc]
  congr 1
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, Bool.decide_or]

theorem coverUpTo_disjoint (W : GMap Loc WatchRange) (key : GoString) (ivls : List adt.IvlS)
    (ivl : adt.IvlS) (h : ivl ∉ ivls) : coverUpTo W key ivls ##ₘ ivlMembers W ivl := by
  intro w h1 h2
  obtain ⟨r, hr, hp⟩ := (mem_membersBy _ _ w).1 h1
  obtain ⟨r', hr', hp'⟩ := (mem_membersBy _ _ w).1 h2
  rw [hr] at hr'; cases hr'
  simp only [decide_eq_true_eq] at hp'
  cases he : r.end? with
  | none => rw [he] at hp'; cases hp'
  | some e =>
    rw [he] at hp hp'
    simp only [Option.map_some, Option.some.injEq] at hp'
    subst hp'
    simp at hp
    exact h hp

/-- With all the overlapping intervals, the members holding the key. -/
theorem coverUpTo_stab (W : GMap Loc WatchRange) (L : List adt.Entry) (hL : RangesOk W L)
    (key : GoString) :
    coverUpTo W key ((adt.stab (key, key ++ go!"\x00") L).map Prod.fst) =
      membersBy W (·.covers key) := by
  refine GMap.ext (fun w => ?_)
  unfold coverUpTo
  rw [membersBy_lookup, membersBy_lookup]
  cases hw : W !! w with
  | none => rfl
  | some r =>
    simp only
    congr 1
    cases he : r.end? with
    | none =>
      rw [covers_none r key he]
      simp [eq_comm]
    | some e =>
      have hc := covers_some r key e he
      have hin : (r.key, e) ∈ L.map Prod.fst := (hL.2 _).2 ⟨w, r, e, hw, he, rfl⟩
      apply propext
      rw [hc]
      simp only [Option.map_some, List.mem_map, Option.some.injEq, reduceCtorEq, decide_false,
        Bool.false_and, Bool.false_or, decide_eq_true_eq]
      unfold adt.stab
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, h⟩
        rw [List.mem_filter] at hz
        rw [← h]; simpa using hz.2
      · intro h0
        obtain ⟨z, hz, hz1⟩ := List.mem_map.1 hin
        refine ⟨z.1, ⟨z, List.mem_filter.2 ⟨hz, ?_⟩, rfl⟩, hz1⟩
        rw [hz1]; simpa using h0

end rangesOk

/-! ## A loop's prefix of a set -/

/-- The keys of `S'` among the first `n` of `keys`. -/
def upTo (keys : List Loc) (n : Nat) (S' : GMap Loc Unit) : GMap Loc Unit :=
  GMap.filter (fun k _ => decide (k ∈ keys.take n)) S'

theorem upTo_zero (keys : List Loc) (S' : GMap Loc Unit) : upTo keys 0 S' = ∅ := by
  refine GMap.ext (fun k => ?_)
  unfold upTo
  simp [GMap.lookup_filter]

theorem upTo_all (keys : List Loc) (S' : GMap Loc Unit)
    (h : ∀ k, k ∈ keys ↔ (S' !! k).isSome) : upTo keys keys.length S' = S' := by
  refine GMap.ext (fun k => ?_)
  unfold upTo
  rw [GMap.lookup_filter, List.take_length]
  cases hk : S' !! k with
  | none => rfl
  | some v =>
    have : k ∈ keys := (h k).2 (by rw [hk]; rfl)
    simp [this]

theorem upTo_succ (keys : List Loc) (S' : GMap Loc Unit) (n : Nat) (key : Loc)
    (hkey : keys[n]? = some key) (hnd : keys.Nodup) (hS : S' !! key = some ()) :
    upTo keys (n + 1) S' = <[key := ()]> (upTo keys n S') ∧ upTo keys n S' !! key = none := by
  have htake : keys.take (n + 1) = keys.take n ++ [key] := by
    rw [List.take_add_one, hkey]; rfl
  have hnot : key ∉ keys.take n := by
    intro hm
    obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hm
    rw [List.getElem_take] at hjk
    have hj' : keys[j]? = some key := by
      rw [List.getElem?_eq_getElem (by simp at hj; omega)]; exact congrArg some hjk
    have := list_nodup_getElem?_inj keys hnd j n key hj' hkey
    simp at hj; omega
  constructor
  · refine GMap.ext (fun k => ?_)
    unfold upTo
    rw [htake]
    by_cases hk : k = key
    · subst hk
      simp [GMap.lookup_filter, hS]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]
      simp [GMap.lookup_filter, hk]
  · unfold upTo
    simp [GMap.lookup_filter, hnot]

/-! ## Ownership -/

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The watcher's fields that are never written after `watch()` builds it (persistent): `key`,
`end` (`nil` for a single key), `startRev`, `id`, `fcs`. -/
def watcherFixed (w : Loc) (r : WatchRange) (fcs : GoSlice) : IProp GF :=
  iprop(⌜w ≠ null⌝ ∗
    ∃ ks es : GoSlice, w.[watcher, go!"key"] ↦□ ks ∗ ks ↦*□ r.key ∗
      w.[watcher, go!"end"] ↦□ es ∗
      (match r.end? with
       | none => ⌜es = slice.nil⌝
       | some e => ⌜es ≠ slice.nil⌝ ∗ es ↦*□ e) ∗
      w.[watcher, go!"startRev"] ↦□ r.startRev ∗ w.[watcher, go!"id"] ↦□ r.id ∗
      w.[watcher, go!"fcs"] ↦□ fcs)

instance watcherFixed_persistent (w : Loc) (r : WatchRange) (fcs : GoSlice) :
    Persistent (watcherFixed (GF := GF) w r fcs) := by
  unfold watcherFixed
  cases r.end? <;> infer_instance

/-- A watcher's fixed fields determine its range. -/
theorem watcherFixed_agree (w : Loc) (r r' : WatchRange) (fcs fcs' : GoSlice) :
    watcherFixed (GF := GF) w r fcs ∗ watcherFixed w r' fcs' ⊢ ⌜r = r' ∧ fcs = fcs'⌝ := by
  unfold watcherFixed
  iintro ⟨⟨%Hn, %ks, %es, Hk, Hks, He, Hes, Hs, Hi, Hf⟩,
    ⟨-, %ks', %es', Hk', Hks', He', Hes', Hs', Hi', Hf'⟩⟩
  icombine Hk Hk' gives %Hk
  subst Hk
  icombine Hks Hks' gives %Hkey
  icombine He He' gives %He
  subst He
  icombine Hs Hs' gives %Hs
  icombine Hi Hi' gives %Hi
  icombine Hf Hf' gives %Hf
  ihave %hend : ⌜r.end? = r'.end?⌝ $$ [Hes Hes']
  · irevert Hes Hes'
    cases r.end? <;> cases r'.end?
    · iintro _ _; ipureintro; rfl
    · iintro %h1 ⟨%h2, _⟩; exact absurd h1 h2
    · iintro ⟨%h1, _⟩ %h2; exact absurd h2 h1
    · iintro ⟨_, H1⟩ ⟨_, H2⟩
      icombine H1 H2 gives %h
      ipureintro; rw [h]
  ipureintro
  obtain ⟨a, b, c, d⟩ := r
  obtain ⟨a', b', c', d'⟩ := r'
  simp_all

/-- The watcher's mutable fields (not the group's: the store's, or a batch's). -/
structure WatcherSt where
  minRev : w64
  victim : Bool
  compacted : Bool
  restore : Bool
  ch : GoChan

/-- The watcher's mutable fields hold `st` (at the fraction `q`: the watchable store's lock
invariant at its read side). -/
def watcherOwn (w : Loc) (st : WatcherSt) (q : Qp := 1) : IProp GF :=
  iprop(w.[watcher, go!"minRev"] ↦{DFrac.own q} st.minRev ∗
    w.[watcher, go!"victim"] ↦{DFrac.own q} st.victim ∗
    w.[watcher, go!"compacted"] ↦{DFrac.own q} st.compacted ∗
    w.[watcher, go!"restore"] ↦{DFrac.own q} st.restore ∗
    w.[watcher, go!"ch"] ↦{DFrac.own q} st.ch)

/-- The watcher set `m` (a `map[*watcher]struct{}`) holds exactly `S` (at the fraction `q`). -/
def ownWatcherSet (m : GoMap) (S : GMap Loc Unit) (q : Qp := 1) : IProp GF :=
  iprop(ownMap m (DFrac.own q) S)

/-- A watcher set or `nil` (an empty set, not owned: Perennial's map points-to is of a non-nil
map, `ownMap_not_nil`). -/
def ownWatcherSetOpt (m : GoMap) (S : GMap Loc Unit) : IProp GF :=
  iprop(⌜m = map.nil ∧ S = ∅⌝ ∨ ownWatcherSet m S)

/-- The key map `km` (`watcherSetByKey`) of the members `W`: one non-empty set per key of a
single-key member, holding the single-key members of that key. -/
def ownKeyMap (km : GoMap) (KM : GMap GoString GoMap) (W : GMap Loc WatchRange) (q : Qp := 1) :
    IProp GF :=
  iprop(ownMap km (DFrac.own q) KM ∗
    ⌜∀ k, (KM !! k).isSome ↔ ∃ w r, W !! w = some r ∧ r.end? = none ∧ r.key = k⌝ ∗
    [∗map] k ↦ m ∈ KM, ownWatcherSet m (keyMembers W k) q)

/-- An entry of the tree is a range set: its value is the set (as an interface value of the
named type `watcherSet`) of the range members of its interval. -/
def rangeSet (W : GMap Loc WatchRange) (z : adt.Entry) (q : Qp := 1) : IProp GF :=
  iprop(∃ m : GoMap, ⌜z.2 = interface.mkOk watcherSet.ty #m⌝ ∗ ownWatcherSet m (ivlMembers W z.1) q)

/-- The group at `wg` holds the members `W` (pointer ↦ range): the all-watchers set, the key
map, the interval tree, consistent with `W`, and the members' fixed fields; at the fraction `q`
(the watchable store's read lock: `ownWatcherGroup_split`, through the tree's pending
fractionality; the group's operations at `1`). -/
def ownWatcherGroup (wg : Loc) (W : GMap Loc WatchRange) (q : Qp := 1) : IProp GF :=
  iprop(∃ (km ws t : Loc) (KM : GMap GoString GoMap) (L : List adt.Entry),
    "Hwg" ∷ typedPointsto wg
      ({ keyWatchers' := km,
         ranges' := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #t,
         watchers' := ws } : watcherGroup) (DFrac.own q) ∗
    "Hws" ∷ ownWatcherSet ws (domSet W) q ∗
    "#Hfixed" ∷ ([∗map] w ↦ r ∈ W, ∃ fcs, watcherFixed w r fcs) ∗
    "Hkm" ∷ ownKeyMap km KM W q ∗
    "Hivt" ∷ adt.ownIvt t L q ∗
    "%HL" ∷ ⌜RangesOk W L⌝ ∗
    "Hranges" ∷ [∗list] z ∈ L, rangeSet W z q)

/-- An `IntervalValue` points-to (what the tree's `Find` and `Stab` lend) as its
fields. -/
theorem iv_split (l : Loc) (v : go_etcd_io.etcd.pkg.v3.adt.IntervalValue) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      l.[go_etcd_io.etcd.pkg.v3.adt.IntervalValue, go!"Ivl"] ↦{dq} v.Ivl' ∗
        l.[go_etcd_io.etcd.pkg.v3.adt.IntervalValue, go!"Val"] ↦{dq} v.Val' := by
  iintro H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  iNamed H
  iframe Ivl Val

/-- The range sets of the entries whose interval's members are unchanged. -/
theorem rangeSets_congr (W W' : GMap Loc WatchRange) (L : List adt.Entry)
    (h : ∀ z ∈ L, ivlMembers W' z.1 = ivlMembers W z.1) :
    ([∗list] z ∈ L, rangeSet (GF := GF) W z) ⊢ [∗list] z ∈ L, rangeSet W' z := by
  apply BigSepL.bigSepL_mono
  intro k z hz
  unfold rangeSet
  rw [h z (List.mem_of_getElem? hz)]

/-- Adding a range member leaves the key map as it is. -/
theorem ownKeyMap_insert_range (km : GoMap) (KM : GMap GoString GoMap) (W : GMap Loc WatchRange)
    (wa : Loc) (r : WatchRange) (hw : W !! wa = none) (he : r.end? ≠ none) :
    ownKeyMap (GF := GF) km KM W ⊢ ownKeyMap km KM (<[wa := r]> W) := by
  unfold ownKeyMap
  iintro ⟨Hkm, %Hdom, Hsets⟩
  iframe Hkm
  isplitl []
  · ipureintro
    intro k
    rw [Hdom k]
    constructor
    · rintro ⟨w, r', hw', he', hk⟩
      refine ⟨w, r', ?_, he', hk⟩
      rw [GMap.lookup_insert_ne _ _ (fun h => by subst h; rw [hw] at hw'; cases hw')]
      exact hw'
    · rintro ⟨w, r', hw', he', hk⟩
      by_cases hww : w = wa
      · subst hww; rw [GMap.lookup_insert] at hw'; cases hw'; exact absurd he' he
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hww)] at hw'
        exact ⟨w, r', hw', he', hk⟩
  iapply (BigSepM.bigSepM_mono (fun {k v} _ => ?_)) $$ Hsets
  rw [keyMembers_insert_ne W wa r k hw (fun h => he h.1)]

/-- Removing a range member leaves the key map as it is. -/
theorem ownKeyMap_delete_range (km : GoMap) (KM : GMap GoString GoMap) (W : GMap Loc WatchRange)
    (wa : Loc) (r : WatchRange) (hw : W !! wa = some r) (he : r.end? ≠ none) :
    ownKeyMap (GF := GF) km KM W ⊢ ownKeyMap km KM (GMap.delete wa W) := by
  unfold ownKeyMap
  iintro ⟨Hkm, %Hdom, Hsets⟩
  iframe Hkm
  isplitl []
  · ipureintro
    intro k
    rw [Hdom k]
    constructor
    · rintro ⟨w, r', hw', he', hk⟩
      by_cases hww : w = wa
      · subst hww; rw [hw] at hw'; cases hw'; exact absurd he' he
      · refine ⟨w, r', ?_, he', hk⟩
        rw [GMap.lookup_delete_ne _ (Ne.symm hww)]; exact hw'
    · rintro ⟨w, r', hw', he', hk⟩
      by_cases hww : w = wa
      · subst hww; rw [GMap.lookup_delete] at hw'; cases hw'
      · rw [GMap.lookup_delete_ne _ (Ne.symm hww)] at hw'
        exact ⟨w, r', hw', he', hk⟩
  iapply (BigSepM.bigSepM_mono (fun {k v} _ => ?_)) $$ Hsets
  rw [keyMembers_delete, GMap.delete_notin]
  rw [keyMembers, membersBy_lookup, hw]
  cases h : r.end? with
  | none => exact absurd h he
  | some _ => simp [h]

/-- The group from its parts. -/
theorem ownWatcherGroup_intro (wg : Loc) (W : GMap Loc WatchRange) (km ws t : Loc)
    (KM : GMap GoString GoMap) (L : List adt.Entry) (hL : RangesOk W L) :
    wg ↦ ({ keyWatchers' := km,
            ranges' := interface.mkOk
              (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #t,
            watchers' := ws } : watcherGroup) ∗
      ownWatcherSet ws (domSet W) ∗ ([∗map] w ↦ r ∈ W, ∃ fcs, watcherFixed w r fcs) ∗
      ownKeyMap km KM W ∗ adt.ownIvt t L 1 ∗ ([∗list] z ∈ L, rangeSet W z) ⊢
    ownWatcherGroup (GF := GF) wg W := by
  iintro ⟨Hwg, Hws, #Hfixed, Hkm, Hivt, Hranges⟩
  unfold ownWatcherGroup
  iexists km, ws, t, KM, L
  simp only [named]
  iframe Hwg Hws Hfixed Hkm Hivt Hranges
  ipureintro; exact hL

/-- The members' fixed fields, out of the group (persistent). -/
theorem ownWatcherGroup_fixed (wg : Loc) (W : GMap Loc WatchRange) :
    ownWatcherGroup (GF := GF) wg W ⊢
      ownWatcherGroup wg W ∗ [∗map] w ↦ r ∈ W, ∃ fcs, watcherFixed w r fcs := by
  iintro Hg
  unfold ownWatcherGroup
  icases Hg with ⟨%km, %ws, %t, %KM, %L, Hg⟩
  iNamed Hg
  isplitl [Hwg Hws Hkm Hivt Hranges]
  · iexists km, ws, t, KM, L
    simp only [named]
    iframe Hwg Hws Hfixed Hkm Hivt Hranges
    ipureintro; exact HL
  iexact Hfixed

theorem ownWatcherGroup_not_null (wg : Loc) (W : GMap Loc WatchRange) :
    ownWatcherGroup (GF := GF) wg W ⊢ ⌜wg ≠ null⌝ := by
  iintro Hg
  unfold ownWatcherGroup
  icases Hg with ⟨%km, %ws, %t, %KM, %L, Hg⟩
  iNamed Hg
  iapply typedPointsto_not_null $$ Hwg

/-- The members are distinct watchers: each one's fixed fields agree with any of its own. -/
theorem ownWatcherGroup_member (wg : Loc) (W : GMap Loc WatchRange) (w : Loc) (r : WatchRange)
    (fcs : GoSlice) :
    ownWatcherGroup (GF := GF) wg W ∗ watcherFixed w r fcs ⊢
      ownWatcherGroup wg W ∗ ⌜W !! w = none ∨ W !! w = some r⌝ := by
  iintro ⟨Hg, #Hw⟩
  icases ownWatcherGroup_fixed wg W $$ Hg with ⟨Hg, #Hfixed⟩
  iframe Hg
  cases h : W !! w with
  | none => ipureintro; exact Or.inl rfl
  | some r' =>
    icases (BigSepM.bigSepM_lookup_acc (m := W) h).1 $$ Hfixed with ⟨⟨%fcs', Hw'⟩, -⟩
    icases watcherFixed_agree w r r' fcs fcs' $$ [Hw Hw'] with %Hag
    · iframe Hw Hw'
    ipureintro; exact Or.inr (by rw [Hag.1])

/-- The group with its all-watchers set at the map `ws` (the group's `watchers` field): `add` and
`delete` keep the map (`syncWatchers` ranges over it while deleting from the group). -/
def ownWatcherGroupAt (wg : Loc) (W : GMap Loc WatchRange) (ws : GoMap) (q : Qp := 1) :
    IProp GF :=
  iprop(∃ (km t : Loc) (KM : GMap GoString GoMap) (L : List adt.Entry),
    "Hwg" ∷ typedPointsto wg
      ({ keyWatchers' := km,
         ranges' := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #t,
         watchers' := ws } : watcherGroup) (DFrac.own q) ∗
    "Hws" ∷ ownWatcherSet ws (domSet W) q ∗
    "#Hfixed" ∷ ([∗map] w ↦ r ∈ W, ∃ fcs, watcherFixed w r fcs) ∗
    "Hkm" ∷ ownKeyMap km KM W q ∗
    "Hivt" ∷ adt.ownIvt t L q ∗
    "%HL" ∷ ⌜RangesOk W L⌝ ∗
    "Hranges" ∷ [∗list] z ∈ L, rangeSet W z q)

/-- The group is the group at its set's map. -/
theorem ownWatcherGroup_at (wg : Loc) (W : GMap Loc WatchRange) (q : Qp) :
    ownWatcherGroup (GF := GF) wg W q ⊣⊢ ∃ ws : GoMap, ownWatcherGroupAt wg W ws q := by
  unfold ownWatcherGroup ownWatcherGroupAt
  constructor
  · iintro H
    icases H with ⟨%km, %ws, %t, %KM, %L, H⟩
    iexists ws, km, t, KM, L
    iexact H
  · iintro H
    icases H with ⟨%ws, %km, %t, %KM, %L, H⟩
    iexists km, ws, t, KM, L
    iexact H

/-- The group at `ws`, its set lent: the rest, and the set. -/
theorem ownWatcherGroupAt_set (wg : Loc) (W : GMap Loc WatchRange) (ws : GoMap) (q : Qp) :
    ownWatcherGroupAt (GF := GF) wg W ws q ⊢
      ownWatcherSet ws (domSet W) q ∗
        (ownWatcherSet ws (domSet W) q -∗ ownWatcherGroupAt wg W ws q) := by
  iintro H
  unfold ownWatcherGroupAt
  icases H with ⟨%km, %t, %KM, %L, H⟩
  iNamed H
  iframe Hws
  iintro Hws
  iexists km, t, KM, L
  simp only [named]
  iframe Hwg Hws Hfixed Hkm Hivt Hranges
  ipureintro; exact HL

/-- The group at `ws` from its parts. -/
theorem ownWatcherGroupAt_intro (wg : Loc) (W : GMap Loc WatchRange) (km ws t : Loc)
    (KM : GMap GoString GoMap) (L : List adt.Entry) (hL : RangesOk W L) :
    wg ↦ ({ keyWatchers' := km,
            ranges' := interface.mkOk
              (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #t,
            watchers' := ws } : watcherGroup) ∗
      ownWatcherSet ws (domSet W) ∗ ([∗map] w ↦ r ∈ W, ∃ fcs, watcherFixed w r fcs) ∗
      ownKeyMap km KM W ∗ adt.ownIvt t L 1 ∗ ([∗list] z ∈ L, rangeSet W z) ⊢
    ownWatcherGroupAt (GF := GF) wg W ws := by
  iintro ⟨Hwg, Hws, #Hfixed, Hkm, Hivt, Hranges⟩
  unfold ownWatcherGroupAt
  iexists km, t, KM, L
  simp only [named]
  iframe Hwg Hws Hfixed Hkm Hivt Hranges
  ipureintro; exact hL

/-- The members are distinct watchers (`ownWatcherGroup_member`, at the set's map). -/
theorem ownWatcherGroupAt_member (wg : Loc) (W : GMap Loc WatchRange) (ws : GoMap) (w : Loc)
    (r : WatchRange) (fcs : GoSlice) :
    ownWatcherGroupAt (GF := GF) wg W ws ∗ watcherFixed w r fcs ⊢
      ownWatcherGroupAt wg W ws ∗ ⌜W !! w = none ∨ W !! w = some r⌝ := by
  iintro ⟨Hg, #Hw⟩
  unfold ownWatcherGroupAt
  icases Hg with ⟨%km, %t, %KM, %L, Hg⟩
  iNamed Hg
  isplitl [Hwg Hws Hkm Hivt Hranges]
  · iexists km, t, KM, L
    simp only [named]
    iframe Hwg Hws Hfixed Hkm Hivt Hranges
    ipureintro; exact HL
  cases h : W !! w with
  | none => ipureintro; exact Or.inl rfl
  | some r' =>
    icases (BigSepM.bigSepM_lookup_acc (m := W) h).1 $$ Hfixed with ⟨⟨%fcs', Hw'⟩, -⟩
    icases watcherFixed_agree w r r' fcs fcs' $$ [Hw Hw'] with %Hag
    · iframe Hw Hw'
    ipureintro; exact Or.inr (by rw [Hag.1])

end reprs

end mvcc
end EtcdGrove
end Perennial
