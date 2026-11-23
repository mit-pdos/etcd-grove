/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/SyncDeps.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
D-SWC2-4 (D54; SWC-2 round S2): the dependencies `lkAlong` gives an `MSync`'s commands are a
permutation of `depsIn` over the `MSync`'s own sequence `syncSeq` (its commands in
`syncOrder`), the base a replica installs at `handleSync`. Next to `syncOrder_lkAlong`
(Graph.lean), in its own module so that Graph's importers are not rebuilt.

The argument: `depsIn` in a sequence without duplicates is characterised by memberships and the
order of conflicting pairs only (`depsIn_char`): `d` is a dependency of `y` iff `d` comes before
`y`, has `y`'s key, one of the two is a put, and every put of the key before `y` is `d` or comes
before `d`. Every pair this mentions conflicts, and `syncOrder_lkAlong` keeps the order of every
conflicting pair, so the two sequences have the same dependencies; both lists have no
duplicates, so they are permutations.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Graph

@[expose] public section

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- In `A ++ x :: B` with `x ∉ A`, what precedes `x` is `A`. -/
theorem precedes_at (A B : List CmdId) (x z : CmdId) (hx : x ∉ A) :
    precedes (A ++ x :: B) z x ↔ z ∈ A := by
  unfold precedes
  rw [List.takeWhile_append_of_pos]
  · simp
  · intro a ha; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]; intro h; subst h; exact hx ha

/-- The order inside a prefix is the order of the whole list. -/
theorem precedes_prefix (A B : List CmdId) (z d : CmdId) (hd : d ∈ A) :
    precedes (A ++ B) z d ↔ precedes A z d := by
  rw [precedes_iff, precedes_iff]
  have hdi : List.idxOf d (A ++ B) = List.idxOf d A := by rw [List.idxOf_append, if_pos hd]
  rw [hdi]
  have hlt := List.idxOf_lt_length_of_mem hd
  constructor
  · rintro ⟨-, hlt'⟩
    by_cases hzA : z ∈ A
    · rw [List.idxOf_append, if_pos hzA] at hlt'; exact ⟨hzA, hlt'⟩
    · rw [List.idxOf_append, if_neg hzA] at hlt'; omega
  · rintro ⟨hz, hlt'⟩
    exact ⟨List.mem_append_left _ hz, by rw [List.idxOf_append, if_pos hz]; exact hlt'⟩

/-- `lkDeps` without duplicates. -/
theorem lkDeps_nodup' (t : Seq) (c : Cmd) (h : (t.map Prod.fst).Nodup) : (lkDeps t c).Nodup := by
  unfold lkDeps
  simp only []
  have hks : (((t.filter (fun p => p.2.key == c.key)).reverse).map Prod.fst).Nodup := by
    rw [List.map_reverse, (List.reverse_perm _).nodup_iff]
    exact (List.filter_sublist.map Prod.fst).nodup h
  have hsince : ((((t.filter (fun p => p.2.key == c.key)).reverse.takeWhile
      (fun p => !p.2.isPut)).map Prod.fst).reverse).Nodup := by
    rw [(List.reverse_perm _).nodup_iff]
    exact ((List.takeWhile_sublist _).map Prod.fst).nodup hks
  have hlast : ((((t.filter (fun p => p.2.key == c.key)).reverse.find?
      (fun p => p.2.isPut)).toList).map Prod.fst).Nodup := by
    cases (((t.filter (fun p => p.2.key == c.key)).reverse.find? (fun p => p.2.isPut))) <;> simp
  split
  · rw [List.nodup_append]
    refine ⟨hlast, hsince, ?_⟩
    intro a ha b hb hab
    subst hab
    cases hf : (((t.filter (fun p => p.2.key == c.key)).reverse.find? (fun p => p.2.isPut))) with
    | none => rw [hf] at ha; simp at ha
    | some p =>
      rw [hf] at ha
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at ha
      subst ha
      rw [List.mem_reverse] at hb
      obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hb
      have hpk := List.mem_of_find?_eq_some hf
      have hpput := List.find?_some hf
      have hqk := List.takeWhile_subset _ hq
      have hqnp := List.all_eq_true.mp List.all_takeWhile q hq
      have := nodup_fst_eq _ hks q p hqk hpk hqp
      subst this
      simp_all
  · exact hlast

theorem depsIn_nodup' (s : Seq) (x : CmdId) (h : (s.map Prod.fst).Nodup) : (depsIn s x).Nodup := by
  unfold depsIn
  split
  · apply lkDeps_nodup'
    unfold before
    exact ((List.takeWhile_sublist _).map Prod.fst).nodup h
  · exact List.nodup_nil

/-- **`depsIn` by memberships and the order of conflicting pairs** (a sequence without
duplicates, `y` in it with command `c`). -/
theorem depsIn_char (L : Seq) (hnd : (L.map Prod.fst).Nodup) (y : CmdId) (c : Cmd)
    (hy : (y, c) ∈ L) (d : CmdId) :
    d ∈ depsIn L y ↔ ∃ cd : Cmd, (d, cd) ∈ L ∧ precedes (L.map Prod.fst) d y ∧
      cd.key = c.key ∧ (cd.isPut ∨ c.isPut) ∧
      ∀ z cz, (z, cz) ∈ L → precedes (L.map Prod.fst) z y → cz.key = c.key → cz.isPut = true →
        z = d ∨ precedes (L.map Prod.fst) z d := by
  obtain ⟨t, u, hL⟩ := List.append_of_mem hy
  subst hL
  have hndt : (t.map Prod.fst).Nodup := by
    rw [List.map_append] at hnd; exact (List.nodup_append.mp hnd).1
  have hyt : y ∉ t.map Prod.fst := by
    rw [List.map_append, List.nodup_append] at hnd
    intro h; exact hnd.2.2 y h y (by simp) rfl
  have hLf : (t ++ (y, c) :: u).map Prod.fst = t.map Prod.fst ++ y :: u.map Prod.fst := by simp
  -- a member of the whole list before `y` is a member of `t`
  have hpre : ∀ z cz, (z, cz) ∈ t ++ (y, c) :: u →
      (precedes ((t ++ (y, c) :: u).map Prod.fst) z y ↔ (z, cz) ∈ t) := by
    intro z cz hz
    rw [hLf, precedes_at _ _ _ _ hyt]
    constructor
    · intro hzt
      obtain ⟨p, hp, hpz⟩ := List.mem_map.mp hzt
      have : p = (z, cz) := nodup_fst_eq _ hnd p (z, cz) (List.mem_append_left _ hp) hz hpz
      rw [← this]; exact hp
    · intro h; exact List.mem_map.mpr ⟨_, h, rfl⟩
  -- the order of two members of `t` is `t`'s
  have hord : ∀ z d, d ∈ t.map Prod.fst →
      (precedes ((t ++ (y, c) :: u).map Prod.fst) z d ↔ precedes (t.map Prod.fst) z d) := by
    intro z d hd
    rw [hLf]; exact precedes_prefix _ _ z d hd
  have hy' : (y, c).1 ∉ t.map Prod.fst := hyt
  rw [show y = (y, c).1 from rfl, depsIn_split t u (y, c) hy']
  simp only []
  rw [mem_lkDeps]
  constructor
  · rintro ⟨t1, q, t2, rfl, rfl, hk, hno, hput⟩
    have hqt : q ∈ t1 ++ q :: t2 := by simp
    have hq1 : q.1 ∉ t1.map Prod.fst := by
      rw [List.map_append, List.map_cons, List.nodup_append] at hndt
      intro h; exact hndt.2.2 q.1 h q.1 (by simp) rfl
    refine ⟨q.2, by simp, ?_, hk, hput, ?_⟩
    · exact (hpre q.1 q.2 (by simp)).mpr hqt
    · intro z cz hz hzy hzk hzp
      have hzt := (hpre z cz hz).mp hzy
      rw [hord z q.1 (by simp)]
      have hf : (t1 ++ q :: t2).map Prod.fst = t1.map Prod.fst ++ q.1 :: t2.map Prod.fst := by simp
      rw [hf, precedes_at _ _ _ _ hq1]
      simp only [List.mem_append, List.mem_cons] at hzt
      rcases hzt with h | h | h
      · exact Or.inr (List.mem_map.mpr ⟨_, h, rfl⟩)
      · exact Or.inl (by rw [← h])
      · have := hno _ h hzk; simp_all
  · rintro ⟨cd, hdL, hdy, hk, hput, hlast⟩
    have hdt := (hpre d cd hdL).mp hdy
    obtain ⟨t1, t2, rfl⟩ := List.append_of_mem hdt
    refine ⟨t1, (d, cd), t2, rfl, rfl, hk, ?_, hput⟩
    intro q' hq' hqk
    cases hqp : q'.2.isPut
    · rfl
    exfalso
    have hqp' : q'.2.isPut = true := hqp
    have hq'L : (q'.1, q'.2) ∈ (t1 ++ (d, cd) :: t2) ++ (y, c) :: u := by simp [hq']
    have hq'y : precedes (((t1 ++ (d, cd) :: t2) ++ (y, c) :: u).map Prod.fst) q'.1 y :=
      (hpre q'.1 q'.2 hq'L).mpr (by simp [hq'])
    have hd1 : d ∉ t1.map Prod.fst := by
      rw [List.map_append, List.map_cons, List.nodup_append] at hndt
      intro h; exact hndt.2.2 d h d (by simp) rfl
    have hnd2 : q'.1 ∉ t1.map Prod.fst ∧ q'.1 ≠ d := by
      rw [List.map_append, List.map_cons, List.nodup_append] at hndt
      have hq2 : q'.1 ∈ t2.map Prod.fst := List.mem_map.mpr ⟨q', hq', rfl⟩
      refine ⟨fun h => hndt.2.2 q'.1 h q'.1 (by simp [hq2]) rfl, fun h => ?_⟩
      have := (List.nodup_cons.mp hndt.2.1).1
      exact this (h ▸ hq2)
    rcases hlast q'.1 q'.2 hq'L hq'y hqk hqp' with h | h
    · exact hnd2.2 h
    · rw [hord q'.1 d (by simp)] at h
      have hf : (t1 ++ (d, cd) :: t2).map Prod.fst = t1.map Prod.fst ++ d :: t2.map Prod.fst := by
        simp
      rw [hf, precedes_at _ _ _ _ hd1] at h
      exact hnd2.1 h

/-- Two sequences with the same pairs, no duplicates, and the same order of every conflicting
pair have the same dependencies (one direction). -/
theorem depsIn_transfer (L1 L2 : Seq) (hnd1 : (L1.map Prod.fst).Nodup)
    (hnd2 : (L2.map Prod.fst).Nodup) (hmem : ∀ p, p ∈ L1 ↔ p ∈ L2)
    (hpair : ∀ a b (ca cb : Cmd), (a, ca) ∈ L1 → (b, cb) ∈ L1 → a ≠ b → ca.key = cb.key →
      (ca.isPut ∨ cb.isPut) → (precedes (L1.map Prod.fst) a b ↔ precedes (L2.map Prod.fst) a b))
    (y : CmdId) (c : Cmd) (hy : (y, c) ∈ L1) (d : CmdId) (hd : d ∈ depsIn L1 y) :
    d ∈ depsIn L2 y := by
  rw [depsIn_char L1 hnd1 y c hy] at hd
  rw [depsIn_char L2 hnd2 y c ((hmem _).mp hy)]
  obtain ⟨cd, hdL, hdy, hk, hput, hlast⟩ := hd
  have hdy' : d ≠ y := fun h => precedes_irrefl _ _ (h ▸ hdy)
  refine ⟨cd, (hmem _).mp hdL, (hpair d y cd c hdL hy hdy' hk hput).mp hdy, hk, hput, ?_⟩
  intro z cz hz hzy hzk hzp
  have hz1 := (hmem _).mpr hz
  have hzy' : z ≠ y := fun h => precedes_irrefl _ _ (h ▸ hzy)
  have hzy1 := (hpair z y cz c hz1 hy hzy' hzk (Or.inl hzp)).mpr hzy
  rcases hlast z cz hz1 hzy1 hzk hzp with h | h
  · exact Or.inl h
  · have hzd : z ≠ d := fun e => precedes_irrefl _ _ (e ▸ h)
    exact Or.inr ((hpair z d cz cd hz1 hdL hzd (hzk.trans hk.symm) (Or.inl hzp)).mp h)

/-- The pairs of `syncSeq (lkAlong cs)` are `cs`'s. -/
theorem syncSeq_lkAlong_mem (cs : Seq) (hnd : (cs.map Prod.fst).Nodup) (p : CmdId × Cmd) :
    p ∈ syncSeq (lkAlong cs) ↔ p ∈ cs := by
  obtain ⟨hmO, -, -⟩ := syncOrder_lkAlong cs hnd
  have hids := lkAlong_ids cs
  -- an entry of `lkAlong cs` gives its pair of `cs`
  have hent : ∀ q ∈ lkAlong cs, (q.1, q.2.1) ∈ cs := by
    intro q hq; rw [← hids]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  unfold syncSeq
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, -, hx⟩
    cases hf : (lkAlong cs).find? (·.1 == x) with
    | none => rw [hf] at hx; simp at hx
    | some q =>
      rw [hf] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      subst hx
      have hq1 : q.1 = x := by simpa using List.find?_some hf
      have := hent q (List.mem_of_find?_eq_some hf)
      rw [hq1] at this; exact this
  · intro hp
    have hpO : p.1 ∈ syncOrder (lkAlong cs) := (hmO p.1).mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
    refine ⟨p.1, hpO, ?_⟩
    obtain ⟨q0, hq0, hq0e⟩ : ∃ q0 ∈ lkAlong cs, (q0.1, q0.2.1) = p := by
      rw [← hids] at hp; exact List.mem_map.mp hp
    cases hf : (lkAlong cs).find? (·.1 == p.1) with
    | none =>
      exfalso
      have := List.find?_eq_none.mp hf q0 hq0
      simp [← hq0e] at this
    | some q =>
      simp only [Option.map_some, Option.some.injEq]
      have hq1 : q.1 = p.1 := by simpa using List.find?_some hf
      have hqc := hent q (List.mem_of_find?_eq_some hf)
      have := nodup_fst_eq cs hnd (q.1, q.2.1) p hqc hp hq1
      rw [← this, hq1]

/-- The ids of `syncSeq (lkAlong cs)` are `syncOrder`'s. -/
theorem syncSeq_lkAlong_fst (cs : Seq) (hnd : (cs.map Prod.fst).Nodup) :
    (syncSeq (lkAlong cs)).map Prod.fst = syncOrder (lkAlong cs) := by
  obtain ⟨hmO, -, -⟩ := syncOrder_lkAlong cs hnd
  have hids := lkAlong_ids cs
  have hall : ∀ x ∈ syncOrder (lkAlong cs),
      ((lkAlong cs).find? (·.1 == x)).isSome := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ((hmO x).mp hx)
    rw [← hids] at hp
    obtain ⟨q0, hq0, hq0e⟩ := List.mem_map.mp hp
    rw [List.find?_isSome]
    exact ⟨q0, hq0, by simp [← hq0e]⟩
  unfold syncSeq
  generalize syncOrder (lkAlong cs) = O at hall
  induction O with
  | nil => rfl
  | cons x O ih =>
    rw [List.filterMap_cons]
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hall x List.mem_cons_self)
    rw [hq]
    simp only [Option.map_some, List.map_cons]
    rw [ih (fun y hy => hall y (List.mem_cons_of_mem x hy))]

/-- **D-SWC2-4**: an `MSync` command's dependencies (`lkAlong`'s, along a sequence `cs` without
duplicates) are a permutation of its `depsIn` over the `MSync`'s sequence `syncSeq`. -/
theorem lkAlong_deps_perm (cs : Seq) (hnd : (cs.map Prod.fst).Nodup) (y : CmdId) (c : Cmd)
    (D : List CmdId) (hm : (y, c, D) ∈ lkAlong cs) :
    D.Perm (depsIn (syncSeq (lkAlong cs)) y) := by
  obtain ⟨hmO, hndO, hpairs⟩ := syncOrder_lkAlong cs hnd
  obtain ⟨t, q, u, hcs, he⟩ := lkAlong_mem cs _ hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hq1 : q.1 ∉ t.map Prod.fst := by
    rw [hcs, List.map_append, List.nodup_append] at hnd
    intro h; exact hnd.2.2 q.1 h q.1 (by simp) rfl
  have hD : lkDeps t q.2 = depsIn cs q.1 := by rw [hcs, depsIn_split t u q hq1]
  rw [hD]
  have hfst := syncSeq_lkAlong_fst cs hnd
  have hnd2 : ((syncSeq (lkAlong cs)).map Prod.fst).Nodup := by rw [hfst]; exact hndO
  have hmem := syncSeq_lkAlong_mem cs hnd
  have hqL : (q.1, q.2) ∈ cs := by rw [hcs]; simp
  apply (List.perm_ext_iff_of_nodup (depsIn_nodup' cs _ hnd) (depsIn_nodup' _ _ hnd2)).mpr
  intro d
  constructor
  · apply depsIn_transfer cs _ hnd hnd2 (fun p => (hmem p).symm) _ q.1 q.2 hqL d
    intro a b ca cb ha hb hab hk hput
    rw [hfst]; exact (hpairs a b ca cb ha hb hab hk hput).symm
  · apply depsIn_transfer _ cs hnd2 hnd hmem _ q.1 q.2 ((hmem _).mpr hqL) d
    intro a b ca cb ha hb hab hk hput
    rw [hfst]; exact hpairs a b ca cb ((hmem _).mp ha) ((hmem _).mp hb) hab hk hput

end sp

end Perennial.github_com.imdea_software.swiftpaxos
