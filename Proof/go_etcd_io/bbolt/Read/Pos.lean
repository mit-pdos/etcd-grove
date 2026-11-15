/-
The read path's (U6, `notes/bbolt-proof-plan.md`) cursor positions over a reader's bucket: a
stack of page references from the bucket's root names a position in the bucket's entries in
order (`rEnts`: the entries of `bktLeaves`, as (leaf, index) pairs), `rPosAt`; and the moves
`first`/`next` make on it (the up-loop's end, the descent's start), by fuel induction as
`rRoute_tree`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.BktOK

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pos
variable [GooseExts]
variable {v : View} {bv : List w8} {pp : Loc}

/-- The leaves below position `pid` (fuel `n`) of the reader bucket whose value is `bv`. -/
def rLeaves (v : View) (bv : List w8) (n pid : Nat) : List (List w8) :=
  if inBucketRoot bv = 0 then [inlinePage bv] else leavesF n v.pages pid

/-- A nested bucket's entry (`ForEachBucket`'s and `bktNames`' test). -/
def entBkt (x : List w8 × Nat) : Bool := decide (leafFlags x.1 x.2 % 2 = bucketLeafFlag)

/-- **A stack prefix** from position `pid` (fuel `n`) of branch references down to position
`pid'` (fuel `m`), with `o` entries before it. -/
def rPreF (v : View) (bv : List w8) (pp : Loc) :
    Nat → Nat → List elemRef → Nat → Nat → Nat → Prop
  | n, pid, [], m, pid', o => m = n ∧ pid' = pid ∧ o = 0
  | n, pid, e :: es, m, pid', o => ∃ n' pg j o', n = n' + 1 ∧ rBrAt v bv pp pid e pg j ∧
      rPreF v bv pp n' (branchPgid pg j) es m pid' o' ∧ o = entsBefore v.pages n' pg j + o'

/-- A stack below position `pid` at its end: every element's index at least its count less one
(`next`'s up-loop found no element to move). -/
def rEndF (v : View) (bv : List w8) (pp : Loc) : Nat → Nat → List elemRef → Prop
  | 0, _, _ => False
  | _ + 1, _, [] => False
  | _ + 1, pid, [e] => ∃ pg, rPageAt v bv pp pid = some (e.page', pg) ∧
      (pageCount pg : Int) - 1 ≤ sint.Z e.index'
  | n + 1, pid, e :: e' :: es => ∃ pg, rPageAt v bv pp pid = some (e.page', pg) ∧
      (pageCount pg : Int) - 1 ≤ sint.Z e.index' ∧
      rEndF v bv pp n (branchPgid pg (sint.Z e.index').toNat) (e' :: es)

/-- The top element of a stack about to descend (`goToFirstElementOnTheStack`) at position `pid`
(fuel `m`), its descent to land at entry `t` below it: a branch at index `j` (the entries before
child `j`), or a leaf at index `t` (its first or one of its entries). -/
def rHdF (v : View) (bv : List w8) (pp : Loc) (m pid : Nat) (e : elemRef) (t : Nat) : Prop :=
  (∃ pg j, rBrAt v bv pp pid e pg j ∧ t = entsBefore v.pages (m - 1) pg j) ∨
  (∃ pg, rLfAt v bv pp pid e pg t ∧ (t = 0 ∨ t < pageCount pg))

/-- A stack landed on a (well-formed) leaf: its top at index `0` or on an entry. -/
def rLanded (v : View) (bv : List w8) (pp : Loc) (els : List elemRef) : Prop :=
  ∃ e pidL pg idx, els.getLast? = some e ∧ rLfAt v bv pp pidL e pg idx ∧
    (idx = 0 ∨ idx < pageCount pg) ∧ leafWF pg pg.length ∧ 16 ≤ pg.length

/-- A stack whose top is past its (well-formed) leaf's entries (`keyValue` returns nil). -/
def rOffEnt (v : View) (bv : List w8) (pp : Loc) (els : List elemRef) : Prop :=
  ∃ e pidL pg idx, els.getLast? = some e ∧ rLfAt v bv pp pidL e pg idx ∧ pageCount pg ≤ idx ∧
    leafWF pg pg.length ∧ 16 ≤ pg.length

/-! ### Basic facts -/

theorem pageCount_lt (pg : List w8) : pageCount pg < 2 ^ 16 := by
  unfold pageCount; exact BitVec.isLt _

theorem entCount_append (A B : List (List w8)) : entCount (A ++ B) = entCount A + entCount B := by
  simp [entCount]

theorem entCount_single (pg : List w8) : entCount [pg] = pageCount pg := by
  simp [entCount, lEnts]

theorem entsBefore_succ (P : Pages) (n : Nat) (pg : List w8) (j : Nat) :
    entsBefore P n pg (j + 1) = entsBefore P n pg j + entCount (leavesF n P (branchPgid pg j)) := by
  unfold entsBefore
  rw [List.range_succ, List.flatMap_append, entCount_append]
  simp

theorem entsBefore_zero (P : Pages) (n : Nat) (pg : List w8) : entsBefore P n pg 0 = 0 := by
  simp [entsBefore, entCount]

theorem rPageAt_tree (v : View) (bv : List w8) (pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (hi : inBucketRoot bv ≠ 0) (h : rPageAt v bv pp pid = some (l, pg)) :
    v.pages !! pid = some pg ∧ l = pageLoc v pid := by
  unfold rPageAt at h
  rw [if_neg hi] at h
  obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hpg, rfl⟩

theorem rPageAt_inline (v : View) (bv : List w8) (pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (hi : inBucketRoot bv = 0) (h : rPageAt v bv pp pid = some (l, pg)) :
    pid = 0 ∧ pg = inlinePage bv ∧ l = pp := by
  unfold rPageAt at h
  rw [if_pos hi] at h
  by_cases h0 : pid = 0
  · rw [if_pos h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h0, h.2.symm, h.1.symm⟩
  · rw [if_neg h0] at h; cases h

theorem rPageAt_same {pid : Nat} {l l' : Loc} {pg pg' : List w8}
    (h1 : rPageAt v bv pp pid = some (l, pg)) (h2 : rPageAt v bv pp pid = some (l', pg')) :
    pg = pg' := by
  rw [h1] at h2; exact congrArg Prod.snd (Option.some.inj h2)

/-- The leaves below a leaf position: itself. -/
theorem rLeaves_leaf (v : View) (bv : List w8) (pp : Loc) (n pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) (hfl : pageFlags pg = leafPageFlag) :
    rLeaves v bv (n + 1) pid = [pg] := by
  unfold rLeaves
  by_cases hi : inBucketRoot bv = 0
  · rw [if_pos hi, (rPageAt_inline v bv pp pid l pg hi h).2.1]
  · rw [if_neg hi]
    simp [leavesF, (rPageAt_tree v bv pp pid l pg hi h).1, hfl]

/-- The leaves below a branch position: its children's. -/
theorem rLeaves_branch (v : View) (bv : List w8) (pp : Loc) (n pid : Nat) (l : Loc) (pg : List w8)
    (hi : inBucketRoot bv ≠ 0) (h : rPageAt v bv pp pid = some (l, pg))
    (hfl : pageFlags pg = branchPageFlag) :
    rLeaves v bv (n + 1) pid =
      (List.range (pageCount pg)).flatMap fun c => leavesF n v.pages (branchPgid pg c) := by
  unfold rLeaves
  rw [if_neg hi]
  have hnl : ¬ pageFlags pg = leafPageFlag := by rw [hfl]; simp [branchPageFlag, leafPageFlag]
  simp [leavesF, (rPageAt_tree v bv pp pid l pg hi h).1, hnl]

theorem rLeaves_tree (v : View) (bv : List w8) (n pid : Nat) (hi : inBucketRoot bv ≠ 0) :
    rLeaves v bv n pid = leavesF n v.pages pid := by
  unfold rLeaves; rw [if_neg hi]

/-- The root's leaves are the bucket's. -/
theorem rLeaves_root (v : View) (bv : List w8) :
    rLeaves v bv (rFuel v bv) (inBucketRoot bv) = bktLeaves v.pages bv := by
  unfold rLeaves rFuel bktLeaves treeLeaves
  by_cases hi : inBucketRoot bv = 0 <;> simp [hi]

/-- `next`'s target is the position or one more. -/
theorem rPosF_s : ∀ (n pid : Nat) (B : List elemRef) (i s : Nat), rPosF v bv pp n pid B i s →
    s = i ∨ s = i + 1
  | 0, _, _, _, _, h => absurd h (by simp [rPosF])
  | _ + 1, _, [], _, _, h => absurd h (by simp [rPosF])
  | _ + 1, _, [_], i, s, ⟨pg, _, hs⟩ => by
    by_cases hc : i < pageCount pg
    · rw [if_pos hc] at hs; omega
    · rw [if_neg hc] at hs; omega
  | n + 1, _, _ :: _ :: _, _, _, ⟨_, _, _, _, _, hr, hi, hs⟩ => by
    rcases rPosF_s n _ _ _ _ hr with h | h <;> omega

/-! ### Splitting a stack -/

/-- **A stack is a prefix and a stack below it.** -/
theorem rPosF_append : ∀ (A : List elemRef) (n pid : Nat) (B : List elemRef) (i s : Nat),
    B ≠ [] → (rPosF v bv pp n pid (A ++ B) i s ↔
      ∃ m pid' o i' s', rPreF v bv pp n pid A m pid' o ∧ rPosF v bv pp m pid' B i' s' ∧
        i = o + i' ∧ s = o + s')
  | [], n, pid, B, i, s, _ => by
    simp only [List.nil_append, rPreF]
    constructor
    · intro h; exact ⟨n, pid, 0, i, s, ⟨rfl, rfl, rfl⟩, h, by omega, by omega⟩
    · rintro ⟨m, pid', o, i', s', ⟨rfl, rfl, rfl⟩, h, rfl, rfl⟩
      simpa using h
  | a :: A, 0, pid, B, i, s, _ => by simp [rPosF, rPreF]
  | a :: A, n + 1, pid, B, i, s, hB => by
    obtain ⟨e', es, hes⟩ : ∃ e' es, A ++ B = e' :: es := by
      cases h : A ++ B with
      | nil => exact absurd (List.append_eq_nil_iff.mp h).2 hB
      | cons e' es => exact ⟨e', es, rfl⟩
    rw [List.cons_append, hes]
    simp only [rPosF, rPreF]
    constructor
    · rintro ⟨pg, j, i', s', hbr, hr, rfl, rfl⟩
      rw [← hes] at hr
      obtain ⟨m, pid', o, i'', s'', hp, hr', rfl, rfl⟩ :=
        (rPosF_append A n (branchPgid pg j) B i' s' hB).mp hr
      exact ⟨m, pid', entsBefore v.pages n pg j + o, i'', s'',
        ⟨n, pg, j, o, rfl, hbr, hp, rfl⟩, hr', by omega, by omega⟩
    · rintro ⟨m, pid', o, i', s', ⟨n', pg, j, o', hn, hbr, hp, rfl⟩, hr, rfl, rfl⟩
      cases hn
      refine ⟨pg, j, o' + i', o' + s', hbr, ?_, by omega, by omega⟩
      rw [← hes]
      exact (rPosF_append A n (branchPgid pg j) B _ _ hB).mpr ⟨m, pid', o', i', s', hp, hr, rfl, rfl⟩

/-- A prefix grown by a branch element. -/
theorem rPreF_snoc (A : List elemRef) : ∀ (n pid m pid' o : Nat) (e : elemRef) (pg : List w8)
    (j : Nat), rPreF v bv pp n pid A (m + 1) pid' o → rBrAt v bv pp pid' e pg j →
    rPreF v bv pp n pid (A ++ [e]) m (branchPgid pg j) (o + entsBefore v.pages m pg j) := by
  induction A with
  | nil =>
    intro n pid m pid' o e pg j h hbr
    simp only [rPreF] at h
    obtain ⟨hm, hp, ho⟩ := h
    subst hm hp ho
    refine ⟨m, pg, j, 0, rfl, hbr, ?_, by omega⟩
    simp [rPreF]
  | cons a A ih =>
    intro n pid m pid' o e pg j h hbr
    obtain ⟨n', pg', j', o', hn, hbr', hp, ho⟩ := h
    exact ⟨n', pg', j', o' + entsBefore v.pages m pg j, hn, hbr', ih n' _ m pid' o' e pg j hp hbr,
      by omega⟩

/-- The fuel at the end of a prefix is the start's less its length. -/
theorem rPreF_fuel : ∀ (A : List elemRef) (n pid m pid' o : Nat), rPreF v bv pp n pid A m pid' o →
    m + A.length = n
  | [], _, _, _, _, _, h => by simp only [rPreF] at h; simp [h.1]
  | _ :: A, _, _, _, _, _, ⟨n', _, _, _, hn, _, hp, _⟩ => by
    have := rPreF_fuel A n' _ _ _ _ hp; simp; omega

/-! ### Entries at a position -/

theorem flatMap_range_split_bind {α β : Type} (g : Nat → List α) (f : α → List β) (c j : Nat)
    (hj : j < c) : ∃ D, ((List.range c).flatMap g).flatMap f =
      ((List.range j).flatMap g).flatMap f ++ ((g j).flatMap f ++ D) := by
  obtain ⟨d, rfl⟩ : ∃ d, c = (j + 1) + d := ⟨c - (j + 1), by omega⟩
  rw [List.range_add, List.flatMap_append, List.range_succ, List.flatMap_append]
  refine ⟨(((List.range d).map fun x => j + 1 + x).flatMap g).flatMap f, ?_⟩
  simp [List.flatMap_append, List.append_assoc]

/-- **The entry at a stack's position** (on an entry): its leaf element. -/
theorem rPosF_ent : ∀ (n pid : Nat) (B : List elemRef) (i s : Nat), rPosF v bv pp n pid B i s →
    i < s → ∃ e pidL pg idx, B.getLast? = some e ∧ rLfAt v bv pp pidL e pg idx ∧
      idx < pageCount pg ∧ ((rLeaves v bv n pid).flatMap lEnts)[i]? = some (pg, idx)
  | 0, _, _, _, _, h, _ => absurd h (by simp [rPosF])
  | _ + 1, _, [], _, _, h, _ => absurd h (by simp [rPosF])
  | n + 1, pid, [e], i, s, ⟨pg, hlf, hs⟩, hlt => by
    have hc : i < pageCount pg := by
      by_cases hc : i < pageCount pg
      · exact hc
      · rw [if_neg hc] at hs; omega
    refine ⟨e, pid, pg, i, rfl, hlf, hc, ?_⟩
    rw [rLeaves_leaf v bv pp n pid _ pg hlf.1 hlf.2.2.1]
    simp [lEnts, hc]
  | n + 1, pid, e :: e' :: es, i, s, ⟨pg, j, i', s', hbr, hr, hi, hs⟩, hlt => by
    obtain ⟨e2, pidL, pgL, idx, hlast, hlf, hidx, hget⟩ :=
      rPosF_ent n _ (e' :: es) i' s' hr (by omega)
    refine ⟨e2, pidL, pgL, idx, by rw [List.getLast?_cons_cons]; exact hlast, hlf, hidx, ?_⟩
    rw [rLeaves_branch v bv pp n pid _ pg hbr.1 hbr.2.1 hbr.2.2.2.1]
    rw [rLeaves_tree v bv n _ hbr.1] at hget
    obtain ⟨D, hD⟩ := flatMap_range_split_bind (fun c => leavesF n v.pages (branchPgid pg c)) lEnts
      _ j hbr.2.2.2.2.1
    rw [hD, hi, List.getElem?_append_right (by unfold entsBefore entCount; omega)]
    have : entsBefore v.pages n pg j + i' -
        (((List.range j).flatMap fun c => leavesF n v.pages (branchPgid pg c)).flatMap lEnts).length
        = i' := by unfold entsBefore entCount; omega
    rw [this, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hget).1]
    exact hget

/-- **A stack at its end has gone past every entry below it.** -/
theorem rPosF_end : ∀ (n pid : Nat) (B : List elemRef) (i s : Nat), rPosF v bv pp n pid B i s →
    rEndF v bv pp n pid B → s = entCount (rLeaves v bv n pid)
  | 0, _, _, _, _, h, _ => absurd h (by simp [rPosF])
  | _ + 1, _, [], _, _, h, _ => absurd h (by simp [rPosF])
  | n + 1, pid, [e], i, s, ⟨pg, hlf, hs⟩, ⟨pg', hpa, hle⟩ => by
    rw [hlf.1] at hpa; cases hpa
    rw [rLeaves_leaf v bv pp n pid _ pg hlf.1 hlf.2.2.1, entCount_single]
    have hc := pageCount_lt pg
    have := hlf.2.2.2.1
    have hix : sint.Z e.index' = (i : Int) := by rw [hlf.2.2.2.2]; word
    by_cases hc' : i < pageCount pg
    · rw [if_pos hc'] at hs; omega
    · rw [if_neg hc'] at hs; omega
  | n + 1, pid, e :: e' :: es, i, s, ⟨pg, j, i', s', hbr, hr, hi, hs⟩, ⟨pg', hpa, hle, hend⟩ => by
    obtain ⟨hib, hpa', -, hfl, hj, hix⟩ := hbr
    rw [hpa'] at hpa; cases hpa
    have hc := pageCount_lt pg
    have hsx : sint.Z e.index' = (j : Int) := by rw [hix]; word
    rw [hsx] at hle hend
    simp only [Int.toNat_natCast] at hend
    have hjl : j + 1 = pageCount pg := by omega
    have hs' := rPosF_end n _ _ _ _ hr hend
    rw [rLeaves_tree v bv n _ hib] at hs'
    rw [rLeaves_branch v bv pp n pid _ pg hib hpa' hfl, hs, hs', ← entsBefore_succ, hjl]
    rfl

/-! ### The moves -/

/-- **The descent's step**: a branch on top of a prefix extends it, its child's first element at
index `0` landing on the same entry. -/
theorem rHdF_down (A : List elemRef) (pid m pid' o t : Nat) (e e' : elemRef) (pgc : List w8)
    (hp : rPreF v bv pp (rFuel v bv) pid A m pid' o) (pg : List w8) (j : Nat)
    (hbr : rBrAt v bv pp pid' e pg j) (ht : t = entsBefore v.pages (m - 1) pg j) (hm : 0 < m)
    (hpa : rPageAt v bv pp (branchPgid pg j) = some (e'.page', pgc)) (hn : e'.node' = null)
    (hi0 : e'.index' = W64 0) (hfl : pageFlags pgc = branchPageFlag ∨ pageFlags pgc = leafPageFlag)
    (hc0 : pageFlags pgc = branchPageFlag → 0 < pageCount pgc) :
    rPreF v bv pp (rFuel v bv) pid (A ++ [e]) (m - 1) (branchPgid pg j) (o + t) ∧
      rHdF v bv pp (m - 1) (branchPgid pg j) e' 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at ht ⊢
  subst ht
  refine ⟨rPreF_snoc A _ pid m' pid' o e pg j hp hbr, ?_⟩
  rcases hfl with hfl | hfl
  · left
    refine ⟨pgc, 0, ⟨hbr.1, hpa, hn, hfl, hc0 hfl, by rw [hi0]; rfl⟩, ?_⟩
    rw [entsBefore_zero]
  · right
    exact ⟨pgc, ⟨hpa, hn, hfl, Nat.zero_le _, by rw [hi0]; rfl⟩, Or.inl rfl⟩

/-- **The descent's end**: a leaf on top of a prefix is a stack at the prefix's entries and the
leaf's index. -/
theorem rHdF_leaf (A : List elemRef) (m pid' o t : Nat) (e : elemRef) (pg : List w8)
    (hp : rPreF v bv pp (rFuel v bv) (inBucketRoot bv) A m pid' o) (hm : 0 < m)
    (hlf : rLfAt v bv pp pid' e pg t) :
    rPosAt v bv pp (A ++ [e]) (o + t) (o + (if t < pageCount pg then t + 1 else t)) := by
  unfold rPosAt
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact (rPosF_append A _ _ [e] _ _ (by simp)).mpr ⟨m' + 1, pid', o, t, _, hp, ⟨pg, hlf, rfl⟩,
    rfl, rfl⟩

/-- A stack's prefix and its top (to read the top's page). -/
theorem rPosF_top (A : List elemRef) (n pid : Nat) (e : elemRef) (rest : List elemRef) (i s : Nat)
    (h : rPosF v bv pp n pid (A ++ e :: rest) i s) :
    ∃ m pid' o i' s' pg, rPreF v bv pp n pid A m pid' o ∧ rPosF v bv pp m pid' (e :: rest) i' s' ∧
      i = o + i' ∧ s = o + s' ∧ rPageAt v bv pp pid' = some (e.page', pg) ∧ e.node' = null := by
  obtain ⟨m, pid', o, i', s', hp, hr, hi, hs⟩ := (rPosF_append A n pid _ i s (by simp)).mp h
  refine ⟨m, pid', o, i', s', ?_⟩
  match m, rest, hr with
  | m + 1, [], ⟨pg, hlf, _⟩ => exact ⟨pg, hp, ⟨pg, hlf, ‹_›⟩, hi, hs, hlf.1, hlf.2.1⟩
  | m + 1, e' :: es, ⟨pg, j, i'', s'', hbr, hr', h1, h2⟩ =>
    exact ⟨pg, hp, ⟨pg, j, i'', s'', hbr, hr', h1, h2⟩, hi, hs, hbr.2.1, hbr.2.2.1⟩

theorem rPreF_det : ∀ (A : List elemRef) (n pid m pid' o m2 pid2 o2 : Nat),
    rPreF v bv pp n pid A m pid' o → rPreF v bv pp n pid A m2 pid2 o2 →
    m = m2 ∧ pid' = pid2 ∧ o = o2
| [], _, _, _, _, _, _, _, _, h, h' => by
  simp only [rPreF] at h h'
  obtain ⟨h1, h2, h3⟩ := h; obtain ⟨h1', h2', h3'⟩ := h'
  subst h1 h2 h3 h1' h2' h3'; simp
| e :: A, n, pid, m, pid', o, m2, pid2, o2, ⟨n', pg, j, o', hn, hbr, hp, ho⟩,
    ⟨n2, pg2, j2, o2', hn2, hbr2, hp2, ho2⟩ => by
  have hnn : n' = n2 := by omega
  subst hnn
  have hpg : pg = pg2 := rPageAt_same hbr.2.1 hbr2.2.1
  subst hpg
  have hj : j = j2 := by
    have h1 := hbr.2.2.2.2.2; have h2 := hbr2.2.2.2.2.2
    have := hbr.2.2.2.2.1; have := hbr2.2.2.2.2.1; have := pageCount_lt pg
    rw [h1] at h2; have := congrArg BitVec.toNat h2; simp at this; omega
  subst hj
  obtain ⟨h1, h2, h3⟩ := rPreF_det A n' _ m pid' o' m2 pid2 o2' hp hp2
  exact ⟨h1, h2, by omega⟩


theorem rPosF_det : ∀ (n pid : Nat) (B : List elemRef) (i s i2 s2 : Nat),
    rPosF v bv pp n pid B i s → rPosF v bv pp n pid B i2 s2 → s = s2
| 0, _, _, _, _, _, _, h, _ => absurd h (by simp [rPosF])
| _ + 1, _, [], _, _, _, _, h, _ => absurd h (by simp [rPosF])
| _ + 1, _, [e], i, s, i2, s2, ⟨pg, hlf, hs⟩, ⟨pg2, hlf2, hs2⟩ => by
  have hpg : pg = pg2 := rPageAt_same hlf.1 hlf2.1
  subst hpg
  have hii : i = i2 := by
    have h1 := hlf.2.2.2.2; have h2 := hlf2.2.2.2.2; rw [h1] at h2
    have := hlf.2.2.2.1; have := hlf2.2.2.2.1; have := pageCount_lt pg
    have := congrArg BitVec.toNat h2; simp at this; omega
  subst hii; rw [hs, hs2]
| n + 1, _, e :: e' :: es, i, s, i2, s2, ⟨pg, j, i', s', hbr, hr, _, hs⟩,
    ⟨pg2, j2, i2', s2', hbr2, hr2, _, hs2⟩ => by
  have hpg : pg = pg2 := rPageAt_same hbr.2.1 hbr2.2.1
  subst hpg
  have hj : j = j2 := by
    have h1 := hbr.2.2.2.2.2; have h2 := hbr2.2.2.2.2.2
    have := hbr.2.2.2.2.1; have := hbr2.2.2.2.2.1; have := pageCount_lt pg
    rw [h1] at h2; have := congrArg BitVec.toNat h2; simp at this; omega
  subst hj
  rw [hs, hs2, rPosF_det n _ _ _ _ _ _ hr hr2]


/-- **The positions below a prefix are well-formed** (and within the height bound). -/
theorem rPreF_tree (pht : Nat → Nat) (hht : pageHts v.pages pht) (A : List elemRef) :
    ∀ (n pid m pid' o : Nat), rPreF v bv pp n pid A m pid' o → rTree v bv pid →
      (inBucketRoot bv = 0 ∨ pht pid < n) → rTree v bv pid' ∧ (inBucketRoot bv = 0 ∨ pht pid' < m) := by
  induction A with
  | nil =>
    intro n pid m pid' o h ht hh
    simp only [rPreF] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ht, hh⟩
  | cons a A ih =>
    intro n pid m pid' o h ht hh
    obtain ⟨n', pg, j, o', rfl, hbr, hp, -⟩ := h
    obtain ⟨l, pg', hpa, -, hpg⟩ := rTree_page v bv pp pid ht
    have hpg' := rPageAt_same hbr.2.1 hpa
    subst hpg'
    rcases hpg with ⟨hl, -⟩ | ⟨-, hi, hpv, -, -, hch⟩
    · rw [hbr.2.2.2.1] at hl; simp [branchPageFlag, leafPageFlag] at hl
    · have hc := (hht pid pg hpv).2 hbr.2.2.2.1 j hbr.2.2.2.2.1
      refine ih n' _ m pid' o' hp (hch j hbr.2.2.2.2.1) ?_
      rcases hh with h | h
      · exact absurd h hi
      · right; omega

/-- **A well-formed reader bucket's root** is within the height bound of its fuel. -/
theorem rRoot_ok (pht : Nat → Nat) (hht : pageHts v.pages pht) (hok : rBktOK v bv) :
    rTree v bv (inBucketRoot bv) ∧ (inBucketRoot bv = 0 ∨ pht (inBucketRoot bv) < rFuel v bv) := by
  refine ⟨hok.2.1, ?_⟩
  by_cases hi : inBucketRoot bv = 0
  · exact Or.inl hi
  · right
    unfold rFuel; rw [if_neg hi]
    rcases hok.2.1 with ⟨h, -⟩ | ⟨-, hwm, hw⟩
    · exact absurd h hi
    · exact pht_lt_size v.pages hwm pht hht _ hw

/-- **`next`'s up-loop invariant** at `k` kept elements: the elements from `k` on are at their
end. -/
def rUpInv (v : View) (bv : List w8) (pp : Loc) (els : List elemRef) (s k : Nat) : Prop :=
  k = els.length ∨ ∃ m pid o i' s', rPreF v bv pp (rFuel v bv) (inBucketRoot bv) (els.take k) m pid o ∧
    rPosF v bv pp m pid (els.drop k) i' s' ∧ rEndF v bv pp m pid (els.drop k) ∧ s = o + s'

/-- The up-loop moves past element `k` (at its end). -/
theorem rUpInv_step (els : List elemRef) (i s k : Nat) (hpos : rPosAt v bv pp els i s)
    (hk : k < els.length) (h : rUpInv v bv pp els s (k + 1)) (pid : Nat) (pg : List w8)
    (hpa : rPageAt v bv pp pid = some (els[k].page', pg))
    (hle : (pageCount pg : Int) - 1 ≤ sint.Z els[k].index') : rUpInv v bv pp els s k := by
  right
  have hsplit : els = els.take k ++ els[k] :: els.drop (k + 1) := by simp
  unfold rPosAt at hpos
  rw [hsplit] at hpos
  obtain ⟨m, pid', o, i', s', pg', hp, hr, hi, hs, hpa', -⟩ := rPosF_top _ _ _ _ _ _ _ hpos
  have hpg := rPageAt_det v bv pp pid pid' _ pg pg' hpa hpa'
  subst hpg
  have hdrop : els.drop k = els[k] :: els.drop (k + 1) := by simp
  refine ⟨m, pid', o, i', s', hp, by rw [hdrop]; exact hr, ?_, hs⟩
  rw [hdrop]
  rcases h with h | ⟨m2, pid2, o2, i2, s2, hp2, hr2, he2, hs2⟩
  · -- `k` is the top
    have hd : els.drop (k + 1) = [] := by simp; omega
    rw [hd] at hr ⊢
    match m, hr with
    | m + 1, _ => exact ⟨pg, hpa', hle⟩
  · have htake : els.take (k + 1) = els.take k ++ [els[k]] := by simp [List.take_succ]
    rw [htake] at hp2
    match m, hr with
    | 0, hr => exact absurd hr (by simp [rPosF])
    | m + 1, hr =>
      cases hrest : els.drop (k + 1) with
      | nil => rw [hrest] at hr2; match m2, hr2 with | 0, h => exact absurd h (by simp [rPosF])
      | cons e' es =>
        rw [hrest] at hr hr2 he2
        obtain ⟨pg3, j, i3, s3, hbr, hr3, -, -⟩ := hr
        refine ⟨pg, hpa', hle, ?_⟩
        have hpg3 : pg3 = pg := rPageAt_same hbr.2.1 hpa'
        subst hpg3
        have hjx : (sint.Z els[k].index').toNat = j := by
          rw [hbr.2.2.2.2.2]; have := pageCount_lt pg3; have := hbr.2.2.2.2.1; word
        rw [hjx]
        -- the prefix grown by `els[k]` ends at its child `j`
        have hp3 := rPreF_snoc _ _ _ m pid' o els[k] pg3 j hp hbr
        obtain ⟨-, hpid, -⟩ := rPreF_det _ _ _ _ _ _ _ _ _ hp3 hp2
        rw [← hpid] at he2
        obtain ⟨hm2, -⟩ := rPreF_det _ _ _ _ _ _ _ _ _ hp3 hp2
        rw [← hm2] at he2
        exact he2
/-- The up-loop starts with nothing at its end. -/
theorem rUpInv_start (els : List elemRef) (s : Nat) : rUpInv v bv pp els s els.length :=
  Or.inl rfl

/-- **The up-loop found nothing**: `next` is past every entry. -/
theorem rUpInv_none (els : List elemRef) (i s : Nat) (hpos : rPosAt v bv pp els i s)
    (h : rUpInv v bv pp els s 0) : s = (rEnts v bv).length := by
  rcases h with h | ⟨m, pid, o, i', s', hp, hr, he, hs⟩
  · unfold rPosAt at hpos
    have : els = [] := List.eq_nil_of_length_eq_zero h.symm
    subst this
    match rFuel v bv, hpos with
    | 0, h => exact absurd h (by simp [rPosF])
    | _ + 1, h => exact absurd h (by simp [rPosF])
  · simp only [List.take_zero, rPreF] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    simp only [List.drop_zero] at hr he
    rw [hs, rPosF_end _ _ _ _ _ hr he, rLeaves_root]
    simp [entCount, rEnts]

/-- **The up-loop found element `k`** (below its end): with its index one more, the stack up to
it is ready to descend, landing on `next`'s target. -/
theorem rUpInv_found (els : List elemRef) (i s k : Nat) (hpos : rPosAt v bv pp els i s)
    (hk : k < els.length) (h : rUpInv v bv pp els s (k + 1)) (pid : Nat) (pg : List w8)
    (hpa : rPageAt v bv pp pid = some (els[k].page', pg))
    (hlt : sint.Z els[k].index' < (pageCount pg : Int) - 1) :
    ∃ m pid' o t, rPreF v bv pp (rFuel v bv) (inBucketRoot bv) (els.take k) m pid' o ∧ 0 < m ∧
      rPageAt v bv pp pid' = some (els[k].page', pg) ∧
      rHdF v bv pp m pid' { els[k] with index' := els[k].index' + W64 1 } t ∧ s = o + t := by
  have hsplit : els = els.take k ++ els[k] :: els.drop (k + 1) := by simp
  unfold rPosAt at hpos
  rw [hsplit] at hpos
  obtain ⟨m, pid', o, i', s', pg', hp, hr, hi, hs, hpa', -⟩ := rPosF_top _ _ _ _ _ _ _ hpos
  have hpg := rPageAt_det v bv pp pid pid' _ pg pg' hpa hpa'
  subst hpg
  have hc := pageCount_lt pg
  match m, hr with
  | 0, hr => exact absurd hr (by simp [rPosF])
  | m + 1, hr =>
  refine ⟨m + 1, pid', o, ?_⟩
  cases hrest : els.drop (k + 1) with
  | nil =>
    rw [hrest] at hr
    obtain ⟨pg2, hlf, hs2⟩ := hr
    have hpg2 : pg2 = pg := rPageAt_same hlf.1 hpa'
    subst hpg2
    have := hlf.2.2.2.1
    have hix : sint.Z els[k].index' = (i' : Int) := by rw [hlf.2.2.2.2]; word
    have hic : i' < pageCount pg2 := by omega
    rw [if_pos hic] at hs2
    refine ⟨i' + 1, hp, by omega, hpa', Or.inr ⟨pg2, ⟨hpa', hlf.2.1, hlf.2.2.1, by omega, ?_⟩, Or.inr (by omega)⟩, ?_⟩
    · show els[k].index' + W64 1 = W64 ((i' + 1 : Nat) : Int)
      rw [hlf.2.2.2.2]; push_cast; word
    · omega
  | cons e' es =>
    rw [hrest] at hr
    obtain ⟨pg2, j, i2, s2, hbr, hr2, -, hs2⟩ := hr
    have hpg2 : pg2 = pg := rPageAt_same hbr.2.1 hpa'
    subst hpg2
    have := hbr.2.2.2.2.1
    have hix : sint.Z els[k].index' = (j : Int) := by rw [hbr.2.2.2.2.2]; word
    refine ⟨entsBefore v.pages m pg2 (j + 1), hp, by omega, hpa',
      Or.inl ⟨pg2, j + 1, ⟨hbr.1, hpa', hbr.2.2.1, hbr.2.2.2.1, by omega, ?_⟩, rfl⟩, ?_⟩
    · show els[k].index' + W64 1 = W64 ((j + 1 : Nat) : Int)
      rw [hbr.2.2.2.2.2]; push_cast; word
    · rcases h with h | ⟨m2, pid2, o2, i3, s3, hp2, hr3, he3, hs3⟩
      · rw [h, List.drop_length] at hrest; cases hrest
      have htake : els.take (k + 1) = els.take k ++ [els[k]] := by simp [List.take_succ]
      rw [htake] at hp2
      have hp3 := rPreF_snoc _ _ _ m pid' o els[k] pg2 j hp hbr
      obtain ⟨hm2, hpid, ho⟩ := rPreF_det _ _ _ _ _ _ _ _ _ hp3 hp2
      subst hm2 hpid ho
      rw [hrest] at hr3 he3
      have hs4 := rPosF_end _ _ _ _ _ hr3 he3
      rw [rLeaves_tree v bv _ _ hbr.1] at hs4
      have h5 : s2 = s3 := by
        have := rPosF_det _ _ _ _ _ _ _ hr2 hr3; exact this
      rw [hs, hs2, h5, hs4, entsBefore_succ]
/-- **Where `next` goes from a stack**, by its top leaf: one further on an entry. -/
theorem rPosF_last (n : Nat) : ∀ (pid : Nat) (B : List elemRef) (i s : Nat),
    rPosF v bv pp n pid B i s →
    ∀ (e : elemRef) (pidL : Nat) (pg : List w8) (idx : Nat), B.getLast? = some e →
      rLfAt v bv pp pidL e pg idx → s = (if idx < pageCount pg then i + 1 else i) := by
  induction n with
  | zero => intro pid B i s h; exact absurd h (by simp [rPosF])
  | succ n ih =>
    intro pid B i s h e pidL pg idx hl hlf
    match B, h with
    | [e0], ⟨pg0, hlf0, hs⟩ =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      have hpg := rPageAt_det v bv pp pid pidL _ pg0 pg hlf0.1 hlf.1
      subst hpg
      have hii : i = idx := by
        have h1 := hlf0.2.2.2.2; have h2 := hlf.2.2.2.2; rw [h1] at h2
        have := hlf0.2.2.2.1; have := hlf.2.2.2.1; have := pageCount_lt pg0
        have := congrArg BitVec.toNat h2; simp at this; omega
      subst hii; exact hs
    | e0 :: e' :: es, ⟨pg0, j, i', s', _, hr, hi, hs⟩ =>
      rw [List.getLast?_cons_cons] at hl
      have := ih _ _ _ _ hr e pidL pg idx hl hlf
      rw [hs, hi, this]
      split <;> omega

theorem rPosAt_last (els : List elemRef) (i s : Nat) (h : rPosAt v bv pp els i s) (e : elemRef)
    (pidL : Nat) (pg : List w8) (idx : Nat) (hl : els.getLast? = some e)
    (hlf : rLfAt v bv pp pidL e pg idx) : s = (if idx < pageCount pg then i + 1 else i) :=
  rPosF_last _ _ _ _ _ h e pidL pg idx hl hlf

/-! ### Names -/

theorem bktNames_rEnts (v : View) (bv : List w8) :
    bktNames v.pages bv = ((rEnts v bv).filter entBkt).map fun x => leafKey x.1 x.2 := by
  unfold bktNames rEnts lEnts entBkt
  rw [List.filter_flatMap, List.map_flatMap]
  congr 1; funext pg
  rw [List.filter_map, List.map_map]
  rfl

/-- The nested buckets among the first `i` entries. -/
def bktBefore (v : View) (bv : List w8) (i : Nat) : Nat :=
  (((rEnts v bv).take i).filter entBkt).length

theorem filter_take_get {α : Type} (L : List α) (p : α → Bool) (i : Nat) (x : α)
    (h : L[i]? = some x) (hp : p x = true) :
    (L.filter p)[((L.take i).filter p).length]? = some x := by
  have hi : i < L.length := (List.getElem?_eq_some_iff.mp h).1
  have hsplit : L = L.take i ++ x :: L.drop (i + 1) := by
    have hx : L[i] = x := (List.getElem?_eq_some_iff.mp h).2
    conv => lhs; rw [← List.take_append_drop i L]
    rw [List.drop_eq_getElem_cons hi, hx]
  have hf : L.filter p = (L.take i).filter p ++ x :: (L.drop (i + 1)).filter p := by
    conv => lhs; rw [hsplit]
    simp [List.filter_append, hp]
  rw [hf, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem bktBefore_succ (v : View) (bv : List w8) (i : Nat) (x : List w8 × Nat)
    (h : (rEnts v bv)[i]? = some x) :
    bktBefore v bv (i + 1) = bktBefore v bv i + (if entBkt x then 1 else 0) := by
  unfold bktBefore
  rw [List.take_succ, h, List.filter_append]
  simp only [Option.toList_some, List.length_append]
  cases hb : entBkt x <;> simp [hb]

/-- **The name of a nested bucket at entry `i`** is `bktNames`' at the count before it. -/
theorem bktNames_at (v : View) (bv : List w8) (i : Nat) (pg : List w8) (idx : Nat)
    (h : (rEnts v bv)[i]? = some (pg, idx)) (hb : entBkt (pg, idx) = true) :
    (bktNames v.pages bv)[bktBefore v bv i]? = some (leafKey pg idx) := by
  rw [bktNames_rEnts, List.getElem?_map, bktBefore, filter_take_get _ _ i _ h hb]
  rfl

theorem bktBefore_end (v : View) (bv : List w8) :
    bktBefore v bv (rEnts v bv).length = (bktNames v.pages bv).length := by
  rw [bktNames_rEnts, List.length_map, bktBefore, List.take_length]

theorem bktBefore_le (v : View) (bv : List w8) (i : Nat) :
    bktBefore v bv i ≤ (bktNames v.pages bv).length := by
  rw [bktNames_rEnts, List.length_map, bktBefore]
  exact (List.take_sublist i _).filter entBkt |>.length_le

/-- The entry at a stack's position (on an entry) is `rEnts`'. -/
theorem rPosAt_ent (els : List elemRef) (i s : Nat) (h : rPosAt v bv pp els i s) (hlt : i < s) :
    ∃ e pidL pg idx, els.getLast? = some e ∧ rLfAt v bv pp pidL e pg idx ∧ idx < pageCount pg ∧
      (rEnts v bv)[i]? = some (pg, idx) := by
  obtain ⟨e, pidL, pg, idx, h1, h2, h3, h4⟩ := rPosF_ent _ _ _ _ _ h hlt
  rw [rLeaves_root] at h4
  exact ⟨e, pidL, pg, idx, h1, h2, h3, h4⟩

/-- The entry at a stack's position, by its top leaf. -/
theorem rPosAt_ent' (els : List elemRef) (i s : Nat) (h : rPosAt v bv pp els i s) (hlt : i < s)
    (e : elemRef) (pidL : Nat) (pg : List w8) (idx : Nat) (hl : els.getLast? = some e)
    (hlf : rLfAt v bv pp pidL e pg idx) : (rEnts v bv)[i]? = some (pg, idx) := by
  obtain ⟨e2, pid2, pg2, idx2, hl2, hlf2, -, hget⟩ := rPosAt_ent els i s h hlt
  rw [hl] at hl2; cases hl2
  have hpg := rPageAt_det v bv pp pid2 pidL _ pg2 pg hlf2.1 hlf.1
  subst hpg
  have hii : idx2 = idx := by
    have h1 := hlf2.2.2.2.2; have h2 := hlf.2.2.2.2; rw [h1] at h2
    have := hlf2.2.2.2.1; have := hlf.2.2.2.1; have := pageCount_lt pg2
    have := congrArg BitVec.toNat h2; simp at this; omega
  rw [← hii]; exact hget

end pos

end bbolt
end EtcdGrove
end Perennial
