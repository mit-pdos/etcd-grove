/-
The pure theory of the key index (`Model.lean`): what `kiGet` answers after `kiPut` and
`kiTombstone`, under the well-formedness `KiWf` the code maintains. Lean-first.

**`KiWf ki`**: the generations are not empty as a list, every generation but the last has a
revision, each generation's `created` is its first revision and its `ver` its number of
revisions. Together with "the new revision is above every revision of `ki`" (`KiAbove`), this
is what the lemmas below need:

- `kiGet_kiPut_below`, `kiGet_kiTombstone_below`: a read strictly below the new revision's
  main is unchanged;
- `kiGet_kiPut_above`: a read at or above it sees the new revision, with the last generation's
  create revision (the new revision's if it was empty) and version + 1;
- `kiGet_kiTombstone_above`: a read at or above a tombstone sees nothing;
- `kiGet_top`: a read at or above every revision sees the last generation's last revision, or
  nothing if it is empty.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

theorem W64_add_one (x : Int) : W64 (x + 1) = W64 x + W64 1 := by
  unfold W64; exact BitVec.ofInt_add x 1

/-- The revisions of a key index, in order. -/
def kiRevs (ki : KeyIndex) : List Rev := (ki.gens.map Gen.revs).flatten

/-- A generation as the code builds it: `created` its first revision, `ver` their number. -/
def GenWf (g : Gen) : Prop :=
  g.ver = W64 g.revs.length ∧ (g.revs ≠ [] → g.created = g.revs.headD Rev.zero)

/-- A key index as the code builds it (see the module docstring). -/
structure KiWf (ki : KeyIndex) : Prop where
  ne : ki.gens ≠ []
  nonlast : ∀ i, i + 1 < ki.gens.length → (ki.gens.getD i Gen.empty).revs ≠ []
  gens : ∀ g ∈ ki.gens, GenWf g

/-- `rev` is above every revision of `ki`, main-wise. -/
def KiAbove (ki : KeyIndex) (rev : Rev) : Prop :=
  ∀ r ∈ kiRevs ki, sint.Z r.main ≤ sint.Z rev.main

/-! ### Generations after a put -/

theorem genPut_revs (g : Gen) (rev : Rev) : (genPut g rev).revs = g.revs ++ [rev] := rfl
theorem genPut_ver (g : Gen) (rev : Rev) : (genPut g rev).ver = g.ver + W64 1 := rfl
theorem genPut_created (g : Gen) (rev : Rev) :
    (genPut g rev).created = if g.revs = [] then rev else g.created := rfl

theorem GenWf.put {g : Gen} (h : GenWf g) (rev : Rev) : GenWf (genPut g rev) := by
  refine ⟨?_, ?_⟩
  · rw [genPut_ver, genPut_revs, h.1, List.length_append, List.length_singleton, Int.natCast_add,
      Int.natCast_one, W64_add_one]
  · intro _
    rw [genPut_created, genPut_revs]
    split
    · rename_i he; rw [he]; rfl
    · rename_i he
      rw [h.2 he]
      cases hr : g.revs with
      | nil => exact absurd hr he
      | cons a l => rfl

theorem Gen.empty_revs : Gen.empty.revs = [] := rfl

theorem GenWf.empty : GenWf Gen.empty := ⟨rfl, fun h => absurd rfl h⟩

/-- The generations `kiPut` works on, and its last one. -/
theorem gensOrEmpty_eq_of_ne {gens : List Gen} (h : gens ≠ []) : gensOrEmpty gens = gens := by
  simp [gensOrEmpty, h]

theorem kiPut_gens_of_ne {ki : KeyIndex} (h : ki.gens ≠ []) (rev : Rev) :
    (kiPut ki rev).gens = ki.gens.dropLast ++ [genPut (ki.gens.getLastD Gen.empty) rev] := by
  rw [kiPut_gens, gensOrEmpty_eq_of_ne h]

theorem kiTombstone_gens (ki : KeyIndex) (rev : Rev) :
    (kiTombstone ki rev).gens = (kiPut ki rev).gens ++ [Gen.empty] := rfl

theorem kiTombstone_modified (ki : KeyIndex) (rev : Rev) : (kiTombstone ki rev).modified = rev := rfl

/-! ### List helpers: the last element replaced -/

theorem getD_dropLast_append_lt {α : Type} (l : List α) (x d : α) (i : Nat)
    (hi : i < l.length - 1) : (l.dropLast ++ [x]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [List.length_dropLast]; exact hi), List.getElem?_dropLast,
    ite_eq_left hi]

theorem getD_dropLast_append_last {α : Type} (l : List α) (x d : α) (_h : l ≠ []) :
    (l.dropLast ++ [x]).getD (l.length - 1) d = x := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [List.length_dropLast]; exact Nat.le_refl _),
    List.length_dropLast, Nat.sub_self]
  rfl

theorem length_dropLast_append {α : Type} (l : List α) (x : α) (h : l ≠ []) :
    (l.dropLast ++ [x]).length = l.length := by
  rw [List.length_append, List.length_dropLast, List.length_singleton]
  have := List.length_pos_iff.2 h
  omega

theorem getD_append_lt {α : Type} (l : List α) (x d : α) (i : Nat) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_last {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem getLastD_eq_getD {α : Type} (l : List α) (d : α) (_h : l ≠ []) :
    l.getLastD d = l.getD (l.length - 1) d := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]

theorem getLastD_mem {α : Type} (l : List α) (d : α) (h : l ≠ []) : l.getLastD d ∈ l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  exact List.getLast_mem h

/-! ### The scan, looking only at the generations it visits -/

theorem kiFindGenAux_congr {gens gens' : List Gen} {rev : w64} :
    ∀ fuel : Nat, (∀ i, i < fuel → gens.getD i Gen.empty = gens'.getD i Gen.empty) →
      (∀ i, i < fuel → (i = gens.length - 1 ↔ i = gens'.length - 1)) →
      kiFindGenAux gens rev fuel = kiFindGenAux gens' rev fuel
  | 0, _, _ => rfl
  | cg + 1, h, hl => by
    rw [kiFindGenAux_succ, kiFindGenAux_succ]
    have hcg := h cg (Nat.lt_succ_self _)
    have hlcg := hl cg (Nat.lt_succ_self _)
    have ih := kiFindGenAux_congr (rev := rev) cg (fun i hi => h i (Nat.lt_succ_of_lt hi))
      (fun i hi => hl i (Nat.lt_succ_of_lt hi))
    simp only [hcg, ne_eq, hlcg, ih]

/-! ### The walk after an appended revision -/

theorem genWalk_append_true (revs : List Rev) (rev : Rev) (p : Rev → Bool) (h : p rev = true) :
    genWalk (revs ++ [rev]) p = genWalk revs p := by
  unfold genWalk
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.findIdx?_cons]
  simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_append,
    List.length_singleton]
  cases List.findIdx? (fun r => !p r) revs.reverse with
  | none => rfl
  | some i =>
    simp only [Option.map_some]
    congr 1
    omega

theorem genWalk_append_false (revs : List Rev) (rev : Rev) (p : Rev → Bool) (h : p rev = false) :
    genWalk (revs ++ [rev]) p = (revs.length : Int) := by
  unfold genWalk
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.findIdx?_cons]
  simp only [h, Bool.not_false, ↓reduceIte, List.length_append, List.length_singleton]
  congr 1

/-! ### Facts about a well-formed key index -/

theorem KiWf.last_wf {ki : KeyIndex} (h : KiWf ki) : GenWf (ki.gens.getLastD Gen.empty) :=
  h.gens _ (getLastD_mem _ _ h.ne)

theorem KiWf.len_pos {ki : KeyIndex} (h : KiWf ki) : 0 < ki.gens.length := List.length_pos_iff.2 h.ne

theorem kiRevs_mem {ki : KeyIndex} {g : Gen} (hg : g ∈ ki.gens) {r : Rev} (hr : r ∈ g.revs) :
    r ∈ kiRevs ki := by
  unfold kiRevs
  rw [List.mem_flatten]
  exact ⟨g.revs, List.mem_map_of_mem hg, hr⟩

theorem headD_mem {l : List Rev} (h : l ≠ []) : l.headD Rev.zero ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.mem_cons_self

theorem headD_append_of_ne_nil {l : List Rev} (x : Rev) (h : l ≠ []) :
    (l ++ [x]).headD Rev.zero = l.headD Rev.zero := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-! ### The scan after a put -/

/-- `findGeneration` after `put`: at or above the new revision, the last generation; below it,
as before. -/
theorem kiFindGen_kiPut {ki : KeyIndex} (hwf : KiWf ki) {rev : Rev} (habove : KiAbove ki rev)
    (r : w64) :
    kiFindGen (kiPut ki rev) r =
      if sint.Z rev.main ≤ sint.Z r then some (ki.gens.length - 1) else kiFindGen ki r := by
  have hne := hwf.ne
  have hpos := hwf.len_pos
  unfold kiFindGen
  rw [kiPut_gens_of_ne hne, length_dropLast_append _ _ hne]
  obtain ⟨m, hm⟩ : ∃ m, ki.gens.length = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hlen' : (ki.gens.dropLast ++ [genPut (ki.gens.getLastD Gen.empty) rev]).length - 1 = m := by
    rw [length_dropLast_append _ _ hne, hm, Nat.add_sub_cancel]
  rw [hm, kiFindGenAux_succ, kiFindGenAux_succ, Nat.add_sub_cancel]
  have hlast := getD_dropLast_append_last ki.gens (genPut (ki.gens.getLastD Gen.empty) rev)
    Gen.empty hne
  rw [hm, Nat.add_sub_cancel] at hlast
  have hg : ki.gens.getD m Gen.empty = ki.gens.getLastD Gen.empty := by
    rw [getLastD_eq_getD _ _ hne, hm, Nat.add_sub_cancel]
  have hcongr : kiFindGenAux (ki.gens.dropLast ++ [genPut (ki.gens.getLastD Gen.empty) rev]) r m =
      kiFindGenAux ki.gens r m := by
    apply kiFindGenAux_congr
    · intro i hi
      rw [getD_dropLast_append_lt _ _ _ _ (by omega)]
    · intro i _
      rw [length_dropLast_append _ _ hne]
  simp only [hlast, hg, hlen', hcongr, genPut_revs, ne_eq, not_true_eq_false,
    false_and, ↓reduceIte, hm, Nat.add_sub_cancel]
  by_cases he : (ki.gens.getLastD Gen.empty).revs = []
  · rw [he]
    simp only [List.nil_append, List.headD_cons, List.cons_ne_nil, ↓reduceIte]
    split
    · rename_i hr; simp only [hr, ↓reduceIte]
    · rename_i hr; simp only [hr, ↓reduceIte]
  · rw [headD_append_of_ne_nil _ he]
    have hne' : (ki.gens.getLastD Gen.empty).revs ++ [rev] ≠ [] := by simp
    simp only [he, hne', ↓reduceIte]
    have hfirst := habove _ (kiRevs_mem (getLastD_mem _ _ hne) (headD_mem he))
    by_cases hr : sint.Z rev.main ≤ sint.Z r
    · rw [ite_eq_left hr, ite_eq_left (by omega)]
    · rw [ite_eq_right hr]

/-- `get` after `put`, at or above the new revision: the new revision, its generation's create
revision (the new revision if the generation was empty) and version + 1. -/
theorem kiGet_kiPut_above {ki : KeyIndex} (hwf : KiWf ki) {rev : Rev} (habove : KiAbove ki rev)
    {r : w64} (hr : sint.Z rev.main ≤ sint.Z r) :
    kiGet (kiPut ki rev) r =
      some (rev, (if (ki.gens.getLastD Gen.empty).revs = [] then rev
        else (ki.gens.getLastD Gen.empty).created), (ki.gens.getLastD Gen.empty).ver + W64 1) := by
  have hne := hwf.ne
  have hpos := hwf.len_pos
  unfold kiGet
  rw [kiFindGen_kiPut hwf habove, ite_eq_left hr]
  simp only
  rw [kiPut_gens_of_ne hne, getD_dropLast_append_last _ _ _ hne]
  simp only [genPut_revs, List.append_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceIte]
  have hw := genWalk_append_false (ki.gens.getLastD Gen.empty).revs rev (pAbove r)
    (by simp [pAbove]; omega)
  have hne1 : ((ki.gens.getLastD Gen.empty).revs.length : Int) ≠ -1 := by omega
  simp only [hw, hne1, ↓reduceIte, Int.toNat_natCast, getD_append_last,
    List.length_append, List.length_singleton, genPut_created, genPut_ver]
  rw [show ((((ki.gens.getLastD Gen.empty).revs.length + 1 : Nat) : Int) -
    (((ki.gens.getLastD Gen.empty).revs.length : Nat) : Int) - 1) = 0 by omega]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  word

/-! ### The generation's answer, and a put seen from below -/

/-- What `kiGet` answers from the generation `kiFindGen` found. -/
def genGet (g : Gen) (atRev : w64) : Option (Rev × Rev × w64) :=
  if g.revs = [] then none
  else
    let n := genWalk g.revs (pAbove atRev)
    if n = -1 then none
    else some (g.revs.getD n.toNat Rev.zero, g.created, g.ver - W64 (g.revs.length - n.toNat - 1))

theorem kiGet_eq (ki : KeyIndex) (r : w64) :
    kiGet ki r = (kiFindGen ki r).bind fun gi => genGet (ki.gens.getD gi Gen.empty) r := by
  unfold kiGet genGet
  cases kiFindGen ki r <;> rfl

theorem genWalk_nil (p : Rev → Bool) : genWalk [] p = -1 := rfl

/-- A read strictly below an appended revision's main does not see it. -/
theorem genGet_genPut_below (g : Gen) {rev : Rev} {r : w64} (hr : sint.Z r < sint.Z rev.main) :
    genGet (genPut g rev) r = genGet g r := by
  unfold genGet
  have hw := genWalk_append_true g.revs rev (pAbove r) (by simp [pAbove]; omega)
  simp only [genPut_revs, genPut_ver, genPut_created, List.append_eq_nil_iff, List.cons_ne_self,
    and_false, ↓reduceIte, hw]
  by_cases he : g.revs = []
  · rw [he]
    simp only [genWalk_nil, ↓reduceIte]
  · simp only [he, ↓reduceIte]
    split
    · rfl
    · rename_i hn
      have hrange := genWalk_range g.revs (pAbove r)
      have hlt : (genWalk g.revs (pAbove r)).toNat < g.revs.length := by omega
      rw [getD_append_lt _ _ _ _ hlt, List.length_append, List.length_singleton]
      rw [show (((g.revs.length + 1 : Nat) : Int) - ((genWalk g.revs (pAbove r)).toNat : Int) - 1) =
        ((g.revs.length : Int) - ((genWalk g.revs (pAbove r)).toNat : Int) - 1) + 1 by omega,
        W64_add_one]
      congr 3
      bv_omega

theorem genGet_kiPut_gens {ki : KeyIndex} (hne : ki.gens ≠ []) {rev : Rev} {r : w64}
    (hr : sint.Z r < sint.Z rev.main) (gi : Nat) (hgi : gi < ki.gens.length) :
    genGet ((kiPut ki rev).gens.getD gi Gen.empty) r = genGet (ki.gens.getD gi Gen.empty) r := by
  rw [kiPut_gens_of_ne hne]
  by_cases hlt : gi < ki.gens.length - 1
  · rw [getD_dropLast_append_lt _ _ _ _ hlt]
  · have : gi = ki.gens.length - 1 := by omega
    subst this
    rw [getD_dropLast_append_last _ _ _ hne, genGet_genPut_below _ hr, getLastD_eq_getD _ _ hne]

/-- `get` after `put`, strictly below the new revision's main: unchanged. -/
theorem kiGet_kiPut_below {ki : KeyIndex} (hwf : KiWf ki) {rev : Rev} (habove : KiAbove ki rev)
    {r : w64} (hr : sint.Z r < sint.Z rev.main) : kiGet (kiPut ki rev) r = kiGet ki r := by
  rw [kiGet_eq, kiGet_eq, kiFindGen_kiPut hwf habove, ite_eq_right (by omega)]
  cases h : kiFindGen ki r with
  | none => rfl
  | some gi =>
    simp only [Option.bind_some]
    exact genGet_kiPut_gens hwf.ne hr gi (kiFindGen_lt h)

/-! ### The scan after a tombstone -/

theorem getLastD_append_singleton {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getLastD d = x := by
  rw [List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton]; rfl

/-- `findGeneration` after `tombstone`: at or above the tombstone, nothing; below it, as
before. -/
theorem kiFindGen_kiTombstone {ki : KeyIndex} (hwf : KiWf ki) {rev : Rev} (_habove : KiAbove ki rev)
    (r : w64) :
    kiFindGen (kiTombstone ki rev) r =
      if sint.Z rev.main ≤ sint.Z r then none else kiFindGen ki r := by
  have hne := hwf.ne
  have hpos := hwf.len_pos
  obtain ⟨m, hm⟩ : ∃ m, ki.gens.length = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hlenP : (kiPut ki rev).gens.length = m + 1 := by
    rw [kiPut_gens_of_ne hne, length_dropLast_append _ _ hne, hm]
  have hlenT : (kiTombstone ki rev).gens.length = m + 2 := by
    rw [kiTombstone_gens, List.length_append, hlenP, List.length_singleton]
  have hT1 : (kiTombstone ki rev).gens.getD (m + 1) Gen.empty = Gen.empty := by
    rw [kiTombstone_gens, ← hlenP, getD_append_last]
  have hT0 : (kiTombstone ki rev).gens.getD m Gen.empty = genPut (ki.gens.getLastD Gen.empty) rev := by
    rw [kiTombstone_gens, getD_append_lt _ _ _ _ (by omega), kiPut_gens_of_ne hne,
      show m = ki.gens.length - 1 by omega, getD_dropLast_append_last _ _ _ hne]
  have hg : ki.gens.getD m Gen.empty = ki.gens.getLastD Gen.empty := by
    rw [getLastD_eq_getD _ _ hne, hm, Nat.add_sub_cancel]
  have hcongr : kiFindGenAux (kiTombstone ki rev).gens r m = kiFindGenAux ki.gens r m := by
    apply kiFindGenAux_congr
    · intro i hi
      rw [kiTombstone_gens, getD_append_lt _ _ _ _ (by omega), kiPut_gens_of_ne hne,
        getD_dropLast_append_lt _ _ _ _ (by omega)]
    · intro i hi
      rw [hlenT, hm]
      omega
  unfold kiFindGen
  rw [hlenT, hm, kiFindGenAux_succ, kiFindGenAux_succ, kiFindGenAux_succ]
  have hmm : ¬ m = m + 2 - 1 := by omega
  simp only [hT1, hT0, hg, Gen.empty_revs, ↓reduceIte, hcongr, genPut_revs, List.append_eq_nil_iff,
    List.cons_ne_self, and_false, hlenT, hm, Nat.add_sub_cancel, ne_eq, getLastD_append_singleton,
    not_true_eq_false, false_and, hmm, not_false_eq_true, true_and]
  by_cases hr : sint.Z rev.main ≤ sint.Z r
  · simp only [hr, ↓reduceIte]
  · simp only [hr, ↓reduceIte]
    by_cases he : (ki.gens.getLastD Gen.empty).revs = []
    · rw [he]
      simp only [List.nil_append, List.headD_cons, hr, ↓reduceIte]
    · rw [headD_append_of_ne_nil _ he]
      simp only [he, ↓reduceIte]

theorem kiGet_kiTombstone_above {ki : KeyIndex} (hwf : KiWf ki) {rev : Rev} (habove : KiAbove ki rev)
    {r : w64} (hr : sint.Z rev.main ≤ sint.Z r) : kiGet (kiTombstone ki rev) r = none := by
  rw [kiGet_eq, kiFindGen_kiTombstone hwf habove, ite_eq_left hr]; rfl

theorem kiGet_kiTombstone_below {ki : KeyIndex} (hwf : KiWf ki) {rev : Rev} (habove : KiAbove ki rev)
    {r : w64} (hr : sint.Z r < sint.Z rev.main) : kiGet (kiTombstone ki rev) r = kiGet ki r := by
  rw [kiGet_eq, kiGet_eq, kiFindGen_kiTombstone hwf habove, ite_eq_right (by omega)]
  cases h : kiFindGen ki r with
  | none => rfl
  | some gi =>
    simp only [Option.bind_some]
    have hgi := kiFindGen_lt h
    rw [kiTombstone_gens, getD_append_lt _ _ _ _
      (by rw [kiPut_gens_of_ne hwf.ne, length_dropLast_append _ _ hwf.ne]; exact hgi)]
    exact genGet_kiPut_gens hwf.ne hr gi hgi

/-! ### Well-formedness and the revisions, through a put and a tombstone -/

theorem dropLast_append_getLastD {α : Type} (l : List α) (d : α) (h : l ≠ []) :
    l.dropLast ++ [l.getLastD d] = l := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  exact List.dropLast_concat_getLast h

theorem kiRevs_kiPut {ki : KeyIndex} (hne : ki.gens ≠ []) (rev : Rev) :
    kiRevs (kiPut ki rev) = kiRevs ki ++ [rev] := by
  unfold kiRevs
  rw [kiPut_gens_of_ne hne]
  conv => rhs; rw [← dropLast_append_getLastD ki.gens Gen.empty hne]
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, genPut_revs, List.append_assoc]

theorem kiRevs_kiTombstone {ki : KeyIndex} (hne : ki.gens ≠ []) (rev : Rev) :
    kiRevs (kiTombstone ki rev) = kiRevs ki ++ [rev] := by
  unfold kiRevs
  rw [kiTombstone_gens, List.map_append, List.flatten_append]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, Gen.empty,
    List.append_nil]
  exact kiRevs_kiPut hne rev

theorem KiWf.put {ki : KeyIndex} (hwf : KiWf ki) (rev : Rev) : KiWf (kiPut ki rev) := by
  have hne := hwf.ne
  refine ⟨by rw [kiPut_gens_of_ne hne]; simp, ?_, ?_⟩
  · intro i hi
    rw [kiPut_gens_of_ne hne, length_dropLast_append _ _ hne] at hi
    rw [kiPut_gens_of_ne hne, getD_dropLast_append_lt _ _ _ _ (by omega)]
    exact hwf.nonlast i hi
  · intro g hg
    rw [kiPut_gens_of_ne hne, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact hwf.gens g ((List.dropLast_sublist _).subset hg)
    · rw [hg]; exact hwf.last_wf.put rev

theorem KiWf.tombstone {ki : KeyIndex} (hwf : KiWf ki) (rev : Rev) : KiWf (kiTombstone ki rev) := by
  have hne := hwf.ne
  have hput := hwf.put rev
  refine ⟨by rw [kiTombstone_gens]; simp, ?_, ?_⟩
  · intro i hi
    rw [kiTombstone_gens, List.length_append, List.length_singleton] at hi
    rw [kiTombstone_gens, getD_append_lt _ _ _ _ (by omega)]
    by_cases hlt : i + 1 < (kiPut ki rev).gens.length
    · exact hput.nonlast i hlt
    · have : i = ki.gens.length - 1 := by
        rw [kiPut_gens_of_ne hne, length_dropLast_append _ _ hne] at hi hlt; omega
      rw [this, kiPut_gens_of_ne hne, getD_dropLast_append_last _ _ _ hne, genPut_revs]
      simp
  · intro g hg
    rw [kiTombstone_gens, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact hput.gens g hg
    · rw [hg]; exact GenWf.empty

theorem KiAbove.put {ki : KeyIndex} (hne : ki.gens ≠ []) {rev : Rev} (h : KiAbove ki rev) {rev' : Rev}
    (hle : sint.Z rev.main ≤ sint.Z rev'.main) : KiAbove (kiPut ki rev) rev' := by
  intro r hr
  rw [kiRevs_kiPut hne, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | hr
  · exact Int.le_trans (h r hr) hle
  · rw [hr]; exact hle

theorem KiAbove.tombstone {ki : KeyIndex} (hne : ki.gens ≠ []) {rev : Rev} (h : KiAbove ki rev)
    {rev' : Rev} (hle : sint.Z rev.main ≤ sint.Z rev'.main) : KiAbove (kiTombstone ki rev) rev' := by
  intro r hr
  rw [kiRevs_kiTombstone hne, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | hr
  · exact Int.le_trans (h r hr) hle
  · rw [hr]; exact hle

/-! ### The empty key index -/

/-- A key index with one empty generation: what `kiPut` starts from when there is none, and
what a tombstone leaves behind. -/
def kiEmpty : KeyIndex := { modified := Rev.zero, gens := [Gen.empty] }

theorem kiPut_fresh (rev : Rev) : kiPut KeyIndex.fresh rev = kiPut kiEmpty rev := rfl

theorem KiWf.kiEmpty : KiWf kiEmpty :=
  ⟨by simp [mvcc.kiEmpty], fun i hi => by simp [mvcc.kiEmpty] at hi,
   fun g hg => by simp [mvcc.kiEmpty] at hg; rw [hg]; exact GenWf.empty⟩

theorem KiAbove.kiEmpty (rev : Rev) : KiAbove kiEmpty rev := by
  intro r hr; simp [kiRevs, mvcc.kiEmpty, Gen.empty] at hr

theorem kiGet_kiEmpty (r : w64) : kiGet kiEmpty r = none := rfl

theorem kiLastEmpty_kiEmpty : kiLastEmpty kiEmpty = true := rfl

end mvcc
end EtcdGrove
end Perennial
