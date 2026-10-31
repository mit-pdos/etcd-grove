/-
**What `restoreIntoIndex` rebuilds from a `Key` bucket a compaction job thinned** (`notes/
m2-storage-plan.md`, "The index at a full revision (branch m2-index)"): the index invariant at a
full revision (`IdxCRepN`, `InvIndexCut.lean`) holds of the rebuilt index (`idxRestore_cut`). Pure,
Lean-first; no backend or bbolt fact.

**The bucket's shape** (`entsCutAt L c ents`): the image's `Key` entries are the log's but for, per
key, a prefix of its entries, each deletable by the compaction at `c` (`KeyDel`). The compaction job
deletes the deletable keys in revision order, in batches (`scheduleCompaction`), and a finished
earlier compaction's deletions are deletable at a later one (`KeyDel` grows with `c`), so a finished
compaction at `c`, a leader's bucket mid-job and either after an earlier finished compaction all
have it. A batch may stop between two sub-revisions of one main revision, and one revision may
change a key twice (sibling transactions, `issues/etcd-txn-check-intervals-sibling.md`): no premise
excludes either.

**The rebuild** (`idxRestore`, the code's fold): per key, the first surviving entry is `restore`d
(a put, with its key-value's create revision and version, which are its generation's: `KvMatch`
through `rev_step`) or `restoreTombstone`d (a tombstone: a generation of its own, whose header no
reader reads, `kiNorm`); every later entry is `put`/`tombstone`d as the writer did. So the rebuilt
key index is the log's cut at the key's first surviving revision (`kiCutAt`, up to `kiNorm`), and
that revision is at or before the one compaction at `c` keeps, since every revision before it is
deletable at `c` (`cutLe_of_dropped`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreModel
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreChunks
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndexCut

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## The rebuild, key by key -/

/-- The revision at position `j` of generation `gi`. -/
def revAt (ki : KeyIndex) (gi j : Nat) : Rev := (ki.gens.getD gi Gen.empty).revs.getD j Rev.zero

theorem revAt_def (ki : KeyIndex) (gi j : Nat) :
    revAt ki gi j = (ki.gens.getD gi Gen.empty).revs.getD j Rev.zero := rfl

/-- `r` is a revision of `ki` at a position before `(gi, j)` (one the cut there drops). -/
def RevBefore (ki : KeyIndex) (gi j : Nat) (r : Rev) : Prop :=
  ∃ i' j', (i' < gi ∨ (i' = gi ∧ j' < j)) ∧ i' < ki.gens.length ∧
    j' < (ki.gens.getD i' Gen.empty).revs.length ∧ r = revAt ki i' j'

/-- **The rebuild's invariant for one key** (`K`: the revisions whose entries survive): nothing
rebuilt and no revision of the key survives so far; or the rebuilt key index is the key's cut at its
first surviving revision, every earlier one dropped. -/
def KeyCut (K : Rev → Bool) (ki : KeyIndex) (o : Option KeyIndex) : Prop :=
  (o = none ∧ ∀ r ∈ kiRevs ki, K r = false) ∨
  ∃ gi j, gi < ki.gens.length ∧ j < (ki.gens.getD gi Gen.empty).revs.length ∧
    K (revAt ki gi j) = true ∧ (∀ r, RevBefore ki gi j r → K r = false) ∧
    o.map kiNorm = some (kiNorm (kiCutAt gi j ki))

/-- The rebuild's invariant: sorted, and every key's `KeyCut`. -/
def CutInv (K : Rev → Bool) (evs : List Ev) (idx : IndexM) : Prop :=
  idx.Pairwise idxLess ∧ ∀ k, KeyCut K (kiOfKey evs k) (idxGet idx k)

/-- What `restoreIntoIndex`'s loop body does to what the tree has of the entry's key. -/
def restoreO (e : KvEnt) (o : Option KeyIndex) : Option KeyIndex :=
  match o with
  | some ki =>
    if e.tomb then (if kiLastEmpty ki then some ki else some (kiTombstone ki e.rev))
    else some (kiPut ki e.rev)
  | none => some (if e.tomb then kiRestoreTombstone e.rev else kiRestore e.kv.createRev e.rev e.kv.version)

theorem idxGet_idxRestoreEnt {idx : IndexM} (hs : idx.Pairwise idxLess) (e : KvEnt) (k : GoString) :
    idxGet (idxRestoreEnt idx e) k = if e.kv.key = k then restoreO e (idxGet idx k) else idxGet idx k := by
  unfold idxRestoreEnt
  cases hg : idxGet idx e.kv.key with
  | some ki =>
    simp only
    by_cases ht : e.tomb = true
    · by_cases hle : kiLastEmpty ki = true
      · simp only [ht, hle, ↓reduceIte]
        by_cases hk : e.kv.key = k
        · subst hk; simp [hg, restoreO, ht, hle]
        · simp [hk]
      · simp only [ht, hle, Bool.false_eq_true, ↓reduceIte]
        rw [idxGet_btInsert hs]
        by_cases hk : e.kv.key = k
        · subst hk; simp [hg, restoreO, ht, hle]
        · simp [hk]
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      rw [idxGet_btInsert hs]
      by_cases hk : e.kv.key = k
      · subst hk; simp [hg, restoreO, ht]
      · simp [hk]
  | none =>
    simp only
    rw [idxGet_btInsert hs]
    by_cases hk : e.kv.key = k
    · subst hk; simp [hg, restoreO]
    · simp [hk]

theorem idxRestoreEnt_sorted {idx : IndexM} (hs : idx.Pairwise idxLess) (e : KvEnt) :
    (idxRestoreEnt idx e).Pairwise idxLess := by
  unfold idxRestoreEnt
  split
  · split
    · split
      · exact hs
      · exact btInsert_sorted idxLess_swo hs
    · exact btInsert_sorted idxLess_swo hs
  · exact btInsert_sorted idxLess_swo hs

/-! ### Positions under the writer's step -/

/-- A put or a tombstone that changes the key index (a tombstone of a key whose last generation is
not empty). -/
def EvChanges (ki : KeyIndex) (ev : Ev) : Prop := ev.tomb = true → kiLastEmpty ki = false

theorem kiApply_gens_getD {ki : KeyIndex} (hne : ki.gens ≠ []) {ev : Ev} (hch : EvChanges ki ev)
    {i : Nat} (hi : i < ki.gens.length) :
    (kiApply ki ev).gens.getD i Gen.empty =
      if i + 1 < ki.gens.length then ki.gens.getD i Gen.empty else genPut (ki.gens.getD i Gen.empty) ev.rev := by
  have hput : (kiPut ki ev.rev).gens.getD i Gen.empty =
      if i + 1 < ki.gens.length then ki.gens.getD i Gen.empty else genPut (ki.gens.getD i Gen.empty) ev.rev := by
    rw [kiPut_gens_of_ne hne]
    split
    · rw [getD_dropLast_append_lt _ _ _ _ (by omega)]
    · rw [show i = ki.gens.length - 1 by omega, getD_dropLast_append_last _ _ _ hne,
        getLastD_eq_getD _ _ hne]
  unfold kiApply
  split
  · rename_i ht
    rw [ite_eq_right (by rw [hch ht]; decide), kiTombstone_gens,
      getD_append_lt _ _ _ _ (by rw [kiPut_gens_of_ne hne, length_dropLast_append _ _ hne]; exact hi)]
    exact hput
  · exact hput

theorem kiApply_length {ki : KeyIndex} (hne : ki.gens ≠ []) {ev : Ev} (hch : EvChanges ki ev) :
    ki.gens.length ≤ (kiApply ki ev).gens.length := by
  unfold kiApply
  split
  · rename_i ht
    rw [ite_eq_right (by rw [hch ht]; decide), kiTombstone_gens, kiPut_gens_of_ne hne, List.length_append,
      length_dropLast_append _ _ hne]
    simp
  · rw [kiPut_gens_of_ne hne, length_dropLast_append _ _ hne]; exact Nat.le_refl _

/-- The writer's step keeps every revision of the key index at its position. -/
theorem kiApply_revAt {ki : KeyIndex} (hne : ki.gens ≠ []) {ev : Ev} (hch : EvChanges ki ev)
    {i j : Nat} (hi : i < ki.gens.length) (hj : j < (ki.gens.getD i Gen.empty).revs.length) :
    j < ((kiApply ki ev).gens.getD i Gen.empty).revs.length ∧ revAt (kiApply ki ev) i j = revAt ki i j := by
  rw [revAt_def, revAt_def, kiApply_gens_getD hne hch hi]
  by_cases h : i + 1 < ki.gens.length
  · rw [ite_eq_left h]; exact ⟨hj, rfl⟩
  · rw [ite_eq_right h, genPut_revs]
    refine ⟨by rw [List.length_append]; omega, ?_⟩
    generalize (ki.gens.getD i Gen.empty).revs = rs at hj ⊢
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem RevBefore.of_kiApply {ki : KeyIndex} (hne : ki.gens ≠ []) {ev : Ev} (hch : EvChanges ki ev)
    {gi j : Nat} (hgi : gi < ki.gens.length) (hj : j ≤ (ki.gens.getD gi Gen.empty).revs.length)
    {r : Rev} (h : RevBefore (kiApply ki ev) gi j r) : RevBefore ki gi j r := by
  obtain ⟨i', j', hpos, hi', hj', rfl⟩ := h
  have hi : i' < ki.gens.length := by omega
  have hj2 : j' < (ki.gens.getD i' Gen.empty).revs.length := by
    rcases hpos with hlt | ⟨rfl, hlt⟩
    · rw [kiApply_gens_getD hne hch hi, ite_eq_left (by omega)] at hj'; exact hj'
    · omega
  exact ⟨i', j', hpos, hi, hj2, (kiApply_revAt hne hch hi hj2).2⟩

theorem revAt_mem {ki : KeyIndex} {i j : Nat} (hi : i < ki.gens.length)
    (hj : j < (ki.gens.getD i Gen.empty).revs.length) : revAt ki i j ∈ kiRevs ki := by
  have hm : (ki.gens.getD i Gen.empty).revs.getD j Rev.zero ∈ (ki.gens.getD i Gen.empty).revs := by
    generalize (ki.gens.getD i Gen.empty).revs = rs at hj ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
  have hg : ki.gens.getD i Gen.empty ∈ ki.gens := by rw [getD_lt _ hi]; exact List.getElem_mem hi
  rw [revAt_def]
  exact kiRevs_mem hg hm

/-- The kept case, a key with a surviving revision already: the step on both. -/
theorem keyCut_kept_old (K : Rev → Bool) {ki : KeyIndex} (hwf : KiWf ki) {ev : Ev}
    (hch : EvChanges ki ev) {X : KeyIndex} (h : KeyCut K ki (some X)) :
    KeyCut K (kiApply ki ev) (stepO ev (some X)) := by
  rcases h with ⟨h, -⟩ | ⟨gi, j, hgi, hj, hK, hbef, hX⟩
  · cases h
  have hne := hwf.ne
  have hp : CutPos ki gi j := ⟨hgi, Or.inl hj⟩
  obtain ⟨hj', hrev⟩ := kiApply_revAt hne hch hgi hj
  right
  refine ⟨gi, j, by have := kiApply_length hne hch; omega, hj', by rw [hrev]; exact hK,
    fun r hr => hbef r (hr.of_kiApply hne hch hgi (Nat.le_of_lt hj)), ?_⟩
  rw [stepO_norm ev (o' := some (kiCutAt gi j ki)) (by rw [hX]; rfl)]
  simp only [stepO]
  have hle := kiLastEmpty_cutAt hp
  unfold kiApply
  by_cases ht : ev.tomb = true
  · have hle0 := hch ht
    rw [hle, hle0]
    simp only [ht, ↓reduceIte, Bool.false_eq_true, Option.map_some, kiCutAt_kiTombstone hp]
  · simp only [ht, Bool.false_eq_true, ↓reduceIte, Option.map_some, kiCutAt_kiPut hp]

/-- The dropped case: the step keeps the invariant if no earlier revision of the key survives. -/
theorem keyCut_dropped (K : Rev → Bool) {ki : KeyIndex} (hwf : KiWf ki) {ev : Ev}
    (hch : EvChanges ki ev) (hK : K ev.rev = false) {o : Option KeyIndex}
    (hnone : ∀ r ∈ kiRevs ki, K r = false) (h : KeyCut K ki o) : KeyCut K (kiApply ki ev) o := by
  rcases h with ⟨ho, -⟩ | ⟨gi, j, hgi, hj, hK', -⟩
  · left
    refine ⟨ho, fun r hr => ?_⟩
    unfold kiApply at hr
    split at hr
    · rename_i ht
      rw [ite_eq_right (by rw [hch ht]; decide), kiRevs_kiTombstone hwf.ne] at hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hnone r hr
      · rw [List.mem_singleton] at hr; rw [hr]; exact hK
    · rw [kiRevs_kiPut hwf.ne] at hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hnone r hr
      · rw [List.mem_singleton] at hr; rw [hr]; exact hK
  · rw [hnone _ (revAt_mem hgi hj)] at hK'; cases hK'

/-- The kept case, a key's first surviving revision: what the rebuild makes of it, up to the
headers, is the key index cut there. -/
theorem keyCut_kept_new (K : Rev → Bool) {ki : KeyIndex} (hwf : KiWf ki) {ev : Ev}
    (hch : EvChanges ki ev) (hK : K ev.rev = true) (hnone : ∀ r ∈ kiRevs ki, K r = false)
    {R : KeyIndex}
    (hR : kiNorm R = kiNorm (kiCutAt (ki.gens.length - 1) (ki.gens.getLastD Gen.empty).revs.length
      (kiApply ki ev))) :
    KeyCut K (kiApply ki ev) (some R) := by
  have hne := hwf.ne
  have hpos := hwf.len_pos
  have hlast : ki.gens.length - 1 < ki.gens.length := by omega
  have hgl : ki.gens.getD (ki.gens.length - 1) Gen.empty = ki.gens.getLastD Gen.empty :=
    (getLastD_eq_getD _ _ hne).symm
  have hg := kiApply_gens_getD hne hch hlast
  rw [ite_eq_right (by omega), hgl] at hg
  right
  refine ⟨ki.gens.length - 1, (ki.gens.getLastD Gen.empty).revs.length,
    by have := kiApply_length hne hch; omega, by rw [hg, genPut_revs, List.length_append]; simp, ?_, ?_, by
      show some (kiNorm R) = _; rw [hR]⟩
  · rw [revAt_def, hg, genPut_revs, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self]
    exact hK
  · intro r hr
    have hr' := hr.of_kiApply hne hch hlast (by rw [hgl]; omega)
    obtain ⟨i', j', -, hi', hj', rfl⟩ := hr'
    exact hnone _ (revAt_mem hi' hj')

/-- The cut at the key's new last revision: one generation (two, after a tombstone). -/
theorem kiCutAt_last_kiPut {ki : KeyIndex} (hne : ki.gens ≠ []) (rev : Rev) :
    kiCutAt (ki.gens.length - 1) (ki.gens.getLastD Gen.empty).revs.length (kiPut ki rev) =
      { modified := rev, gens := [genDrop (ki.gens.getLastD Gen.empty).revs.length
          (genPut (ki.gens.getLastD Gen.empty) rev)] } := by
  refine KeyIndex.ext' rfl ?_
  rw [kiCutAt_gens, kiPut_gens_of_ne hne]
  have hl := length_dropLast_append ki.gens (genPut (ki.gens.getLastD Gen.empty) rev) hne
  rw [getD_dropLast_append_last _ _ _ hne]
  generalize ki.gens.dropLast ++ [genPut (ki.gens.getLastD Gen.empty) rev] = G at hl
  have hpos := List.length_pos_iff.2 hne
  apply List.ext_getElem?
  intro t
  simp only [List.getElem?_drop, List.getElem?_set, List.getElem?_singleton]
  grind

theorem kiCutAt_last_kiTombstone {ki : KeyIndex} (hne : ki.gens ≠ []) (rev : Rev) :
    kiCutAt (ki.gens.length - 1) (ki.gens.getLastD Gen.empty).revs.length (kiTombstone ki rev) =
      { modified := rev, gens := [genDrop (ki.gens.getLastD Gen.empty).revs.length
          (genPut (ki.gens.getLastD Gen.empty) rev), Gen.empty] } := by
  have h1 : kiTombstone ki rev = { kiPut ki rev with gens := (kiPut ki rev).gens ++ [Gen.empty] } := rfl
  have hl : ki.gens.length - 1 < (kiPut ki rev).gens.length := by
    rw [kiPut_gens_of_ne hne, length_dropLast_append _ _ hne]
    have := List.length_pos_iff.2 hne; omega
  have hg : (kiCutAt (ki.gens.length - 1) (ki.gens.getLastD Gen.empty).revs.length (kiTombstone ki rev)).gens =
      (kiCutAt (ki.gens.length - 1) (ki.gens.getLastD Gen.empty).revs.length (kiPut ki rev)).gens ++ [Gen.empty] := by
    rw [h1, kiCutAt_appendEmpty hl]
  refine KeyIndex.ext' rfl ?_
  rw [hg, kiCutAt_last_kiPut hne]
  rfl

theorem genDrop_genPut_last (g : Gen) (rev : Rev) :
    genDrop g.revs.length (genPut g rev) =
      { ver := g.ver + W64 1, created := if g.revs = [] then rev.main else g.created, revs := [rev] } := by
  unfold genDrop genPut
  simp

/-! ## One entry, in the log -/

/-- What the log's key index of a key is at a change of revision `log.length` (the first `i` of
its changes applied): well formed, its revisions at or below the revision, and its answer at the
revision the state after those changes (`rev_step`). -/
theorem keyAt_change {log : Log} {cs : List Change}
    (hl : log.length + 1 < 2 ^ 63) (hcs : cs.length < 2 ^ 63)
    (hcsl : ∀ c ∈ log, c.length < 2 ^ 63) (hwf : LogWf' (log ++ [cs])) (k : GoString)
    {i : Nat} (hi : i ≤ cs.length) :
    KiAbove (kiOfKey (evsOf log ++ evsOfRev log.length (cs.take i)) k) ⟨W64 log.length, W64 0⟩ ∧
    KvMatch (log ++ [cs]) (kiGet (kiOfKey (evsOf log ++ evsOfRev log.length (cs.take i)) k) (W64 log.length))
      (findKey k (applyChanges (W64 log.length) (stateAfter log) (cs.take i))) := by
  have hk0 := keyLink_of_rev k log.reverse (by simp; omega)
    (fun c hc => hcsl c (List.mem_reverse.1 hc)) (by rw [List.reverse_reverse]; exact hwf.prefix)
  rw [List.reverse_reverse] at hk0
  obtain ⟨-, hrevs, -, hmatch⟩ := rev_step log cs hl hcs hwf k _ hk0 i hi
  have he : kiOfKey (evsOf log ++ evsOfRev log.length (cs.take i)) k =
      kiFold (kiOfKey (evsOf log) k) (evsOfRev log.length (cs.take i)) k := by
    rw [kiOfKey_eq_kiFold, kiFold_append, ← kiOfKey_eq_kiFold]
  rw [he]
  refine ⟨fun r hr => ?_, hmatch log.length (Nat.le_refl _) (by omega)⟩
  have := hrevs r hr
  simp only
  have h1 : sint.Z r.main = (r.main.toNat : Int) := by word
  have h2 : sint.Z (W64 log.length) = log.length := by word
  omega

/-- A delete the log allows finds a key index whose last generation is not empty. -/
theorem lastEmpty_false_at_del {log : Log} {cs : List Change}
    (hl : log.length + 1 < 2 ^ 63) (hcs : cs.length < 2 ^ 63)
    (hcsl : ∀ c ∈ log, c.length < 2 ^ 63) (hwf : LogWf' (log ++ [cs])) (hne : log ≠ [])
    {i : Nat} (hi : i < cs.length) {k : GoString} (hc : cs[i] = .del k) :
    kiLastEmpty (kiOfKey (evsOf log ++ evsOfRev log.length (cs.take i)) k) = false := by
  obtain ⟨habove, hm⟩ := keyAt_change hl hcs hcsl hwf k (Nat.le_of_lt hi)
  have hpres := hwf.2 log.length cs i k (by simp) (by rw [List.getElem?_eq_getElem hi, hc])
  rw [stateAt_append_lt log cs (by have := List.length_pos_iff.2 hne; omega), stateAt_last] at hpres
  have hwfk := kiOfKey_wf (evsOf log ++ evsOfRev log.length (cs.take i)) k
  rw [kiGet_top hwfk habove] at hm
  unfold kiLastEmpty
  by_cases he : ((kiOfKey (evsOf log ++ evsOfRev log.length (cs.take i)) k).gens.getLastD Gen.empty).revs = []
  · rw [ite_eq_left he] at hm
    rw [KvMatch_none_left hm] at hpres
    simp at hpres
  · simp only [he, decide_false]

/-- **One entry**: the rebuild's step on a change's entry (if it survives) keeps the invariant. -/
theorem cutInv_step {log : Log} {cs : List Change}
    (hl : log.length + 1 < 2 ^ 63) (hcs : cs.length < 2 ^ 63)
    (hcsl : ∀ c ∈ log, c.length < 2 ^ 63) (hwf : LogWf' (log ++ [cs])) (hne : log ≠ [])
    {i : Nat} (hi : i < cs.length) {kv : EtcdKv}
    (hkv : changeKv (W64 log.length) (stateAfter log) cs i = some kv) (K : Rev → Bool)
    (hK : ∀ e₁ ∈ evsOf log ++ evsOfRev log.length (cs.take (i + 1)),
      ∀ e₂ ∈ evsOf log ++ evsOfRev log.length (cs.take (i + 1)),
      e₁.key = e₂.key → Rev.lt e₁.rev e₂.rev → K e₁.rev = true → K e₂.rev = true)
    {idx : IndexM} (h : CutInv K (evsOf log ++ evsOfRev log.length (cs.take i)) idx) :
    CutInv K (evsOf log ++ evsOfRev log.length (cs.take (i + 1)))
      (if K ⟨W64 log.length, W64 i⟩ then
        idxRestoreEnt idx ⟨⟨W64 log.length, W64 i⟩, cs[i].isDel, kv⟩ else idx) := by
  have hci : cs[i]? = some cs[i] := List.getElem?_eq_getElem hi
  have hP : evsOf log ++ evsOfRev log.length (cs.take (i + 1)) =
      (evsOf log ++ evsOfRev log.length (cs.take i)) ++ [{ rev := ⟨W64 log.length, W64 i⟩, change := cs[i] }] := by
    rw [evsOfRev_take_succ _ _ hi, List.append_assoc]
  rw [hP] at hK ⊢
  -- the event and its entry
  have hkk : kv.key = cs[i].key := by
    unfold changeKv at hkv
    rw [hci] at hkv
    generalize cs[i] = c at hkv ⊢
    cases c with
    | put k v l => exact findKey_key hkv
    | del k => cases hkv; rfl
  have hevs_lt : ∀ e ∈ evsOf log ++ evsOfRev log.length (cs.take i),
      Rev.lt e.rev ⟨W64 log.length, W64 i⟩ := by
    intro e he
    have := evsOf_rev_lt log (cs.take i) (by omega) (by simp; omega) e
      (by rw [evsOf_append]; exact he)
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at this
    exact this
  generalize hPdef : evsOf log ++ evsOfRev log.length (cs.take i) = P at *
  generalize hev : ({ rev := ⟨W64 log.length, W64 i⟩, change := cs[i] } : Ev) = ev at *
  have hevrev : ev.rev = ⟨W64 log.length, W64 i⟩ := by rw [← hev]
  have hevkey : ev.key = cs[i].key := by rw [← hev]
  have hevtomb : ev.tomb = cs[i].isDel := by rw [← hev]
  obtain ⟨hs, hk⟩ := h
  -- the event changes its key's index (a delete is of a present key)
  have hch : EvChanges (kiOfKey P ev.key) ev := by
    intro ht
    rw [hevtomb] at ht
    generalize hc : cs[i] = c at ht hevkey
    cases c with
    | put => cases ht
    | del k =>
      rw [hevkey, ← hPdef]
      exact lastEmpty_false_at_del hl hcs hcsl hwf hne hi hc
  -- no surviving revision of the key before a dropped one
  have hnone_of : K ev.rev = false → ∀ r ∈ kiRevs (kiOfKey P ev.key), K r = false := by
    intro hKe r hr
    cases hKr : K r with
    | false => rfl
    | true =>
      obtain ⟨e₁, he₁, hr₁, hk₁⟩ := kiRevs_kiOfKey hr
      have := hK e₁ (List.mem_append_left _ he₁) ev (List.mem_append_right _ (List.mem_singleton_self _))
        hk₁ (by rw [hevrev]; exact hevs_lt e₁ he₁) (by rw [hr₁]; exact hKr)
      rw [hKe] at this; cases this
  have hwfk := kiOfKey_wf P ev.key
  rw [← hevrev]
  by_cases hKe : K ev.rev = true
  · rw [ite_eq_left hKe]
    have hent : (⟨ev.rev, cs[i].isDel, kv⟩ : KvEnt).kv.key = ev.key := by rw [hkk, hevkey]
    refine ⟨idxRestoreEnt_sorted hs _, fun k => ?_⟩
    rw [kiOfKey_append, idxGet_idxRestoreEnt hs, hent]
    by_cases hkey : ev.key = k
    · subst hkey
      rw [ite_eq_left rfl, ite_eq_left rfl]
      cases hg : idxGet idx ev.key with
      | some X =>
        have := keyCut_kept_old K hwfk hch (X := X) (by rw [← hg]; exact hk ev.key)
        have hro : restoreO ⟨ev.rev, cs[i].isDel, kv⟩ (some X) = stepO ev (some X) := by
          simp only [restoreO, stepO, hevtomb]
        rw [hro]; exact this
      | none =>
        have hk0 := hk ev.key
        rw [hg] at hk0
        have hnone : ∀ r ∈ kiRevs (kiOfKey P ev.key), K r = false := by
          rcases hk0 with ⟨-, h0⟩ | ⟨gi, j, -, -, -, -, h0⟩
          · exact h0
          · cases h0
        simp only [restoreO]
        apply keyCut_kept_new K hwfk hch hKe hnone
        have hne := hwfk.ne
        unfold kiApply
        by_cases ht : ev.tomb = true
        · -- a tombstone: `restoreTombstone`'s generation, up to its header
          have hle := hch ht
          have ht2 : cs[i].isDel = true := by rw [← hevtomb]; exact ht
          simp only [ht2, ht, hle, ↓reduceIte, Bool.false_eq_true]
          rw [kiCutAt_last_kiTombstone hne, genDrop_genPut_last]
          refine kiNorm_eq_of (by rfl) (by rfl) ?_ (by rfl)
          intro t ht'
          simp only [kiRestoreTombstone, List.length_cons, List.length_nil] at ht'
          rw [show t = 0 by omega]
          simp [genNorm, kiRestoreTombstone]
        · -- a put: `restore` with the key-value's create revision and version, its generation's
          have ht' : cs[i].isDel = false := by rw [← hevtomb]; simpa using ht
          have hcput : ∃ k' v l, cs[i] = .put k' v l := by
            cases hc : cs[i] with
            | put k' v l => exact ⟨k', v, l, rfl⟩
            | del k' => rw [hc] at ht'; cases ht'
          obtain ⟨k', v, l, hc⟩ := hcput
          have hk' : ev.key = k' := by rw [hevkey, hc]; rfl
          -- the key-value's create revision and version, from the state after the put
          obtain ⟨-, hm⟩ := keyAt_change hl hcs hcsl hwf ev.key (i := i + 1) (by omega)
          rw [evsOfRev_take_succ _ _ hi, ← List.append_assoc, hPdef, hev, kiOfKey_append,
            ite_eq_left rfl] at hm
          unfold kiApply at hm
          rw [ite_eq_right ht] at hm
          obtain ⟨habove, -⟩ := keyAt_change hl hcs hcsl hwf ev.key (Nat.le_of_lt hi)
          rw [hPdef] at habove
          have habove' : KiAbove (kiOfKey P ev.key) ev.rev := by
            intro r hr; have := habove r hr; rw [hevrev]; exact this
          rw [kiGet_kiPut_above hwfk habove' (by rw [hevrev]; exact Int.le_refl _)] at hm
          have hkv' : findKey ev.key (applyChanges (W64 log.length) (stateAfter log) (cs.take (i + 1))) = some kv := by
            rw [hk']; unfold changeKv at hkv; rw [hci, hc] at hkv; exact hkv
          rw [hkv'] at hm
          obtain ⟨-, hcr, hver, -⟩ := hm
          simp only [ht', ht, Bool.false_eq_true, ↓reduceIte]
          rw [kiCutAt_last_kiPut hne, genDrop_genPut_last]
          rw [hcr, hver]
          rfl
    · rw [ite_eq_right hkey, ite_eq_right hkey]; exact hk k
  · rw [ite_eq_right hKe]
    rw [Bool.not_eq_true] at hKe
    refine ⟨hs, fun k => ?_⟩
    rw [kiOfKey_append]
    by_cases hkey : ev.key = k
    · subst hkey
      rw [ite_eq_left rfl]
      exact keyCut_dropped K hwfk hch hKe (hnone_of hKe) (hk ev.key)
    · rw [ite_eq_right hkey]; exact hk k

/-! ## The whole bucket, filtered -/

theorem evsOfRev_take_mem {m : Nat} {cs : List Change} {i : Nat} {e : Ev}
    (h : e ∈ evsOfRev m (cs.take i)) : e ∈ evsOfRev m cs := by
  unfold evsOfRev at h ⊢
  rw [List.mem_map] at h ⊢
  obtain ⟨⟨x, j⟩, hp, rfl⟩ := h
  refine ⟨(x, j), ?_, rfl⟩
  rw [List.mem_zipIdx_iff_getElem?] at hp ⊢
  rw [List.getElem?_take] at hp
  split at hp
  · exact hp
  · cases hp

/-- **One revision**: the rebuild over its surviving entries keeps the invariant. -/
theorem cutInv_rev {log : Log} {cs : List Change}
    (hl : log.length + 1 < 2 ^ 63) (hcs : cs.length < 2 ^ 63)
    (hcsl : ∀ c ∈ log, c.length < 2 ^ 63) (hwf : LogWf' (log ++ [cs])) (hne : log ≠ [])
    (K : Rev → Bool)
    (hK : ∀ e₁ ∈ evsOf log ++ evsOfRev log.length cs, ∀ e₂ ∈ evsOf log ++ evsOfRev log.length cs,
      e₁.key = e₂.key → Rev.lt e₁.rev e₂.rev → K e₁.rev = true → K e₂.rev = true)
    {idx0 : IndexM} (h0 : CutInv K (evsOf log) idx0) :
    ∀ i, i ≤ cs.length →
      CutInv K (evsOf log ++ evsOfRev log.length (cs.take i))
        ((((List.range i).filterMap fun j =>
            (changeKv (W64 log.length) (stateAfter log) cs j).map fun kv =>
              (⟨⟨W64 log.length, W64 j⟩, (cs.getD j (.del [])).isDel, kv⟩ : KvEnt)).filter
          (fun e => K e.rev)).foldl idxRestoreEnt idx0)
  | 0, _ => by simpa [evsOfRev] using h0
  | i + 1, hi => by
    have hlt : i < cs.length := by omega
    have ih := cutInv_rev hl hcs hcsl hwf hne K hK h0 i (by omega)
    rw [List.range_succ, List.filterMap_append, List.filter_append, List.foldl_append]
    obtain ⟨kv, hkv⟩ := changeKv_isSome (W64 log.length) (stateAfter log) (stateAfter_sorted log) cs hlt
    simp only [List.filterMap_cons, List.filterMap_nil, hkv, Option.map_some]
    rw [show cs.getD i (.del []) = cs[i] by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]]
    have hK' : ∀ e₁ ∈ evsOf log ++ evsOfRev log.length (cs.take (i + 1)),
        ∀ e₂ ∈ evsOf log ++ evsOfRev log.length (cs.take (i + 1)),
        e₁.key = e₂.key → Rev.lt e₁.rev e₂.rev → K e₁.rev = true → K e₂.rev = true := by
      intro e₁ h₁ e₂ h₂
      have sub : ∀ e ∈ evsOf log ++ evsOfRev log.length (cs.take (i + 1)),
          e ∈ evsOf log ++ evsOfRev log.length cs := by
        intro e he
        rcases List.mem_append.1 he with he | he
        · exact List.mem_append_left _ he
        · exact List.mem_append_right _ (evsOfRev_take_mem he)
      exact hK e₁ (sub e₁ h₁) e₂ (sub e₂ h₂)
    have := cutInv_step hl hcs hcsl hwf hne hlt hkv K hK' ih
    rw [List.filter_cons, List.filter_nil]
    by_cases hKi : K ⟨W64 log.length, W64 i⟩ = true
    · simp only [hKi, ↓reduceIte, List.foldl_cons, List.foldl_nil] at this ⊢
      exact this
    · simp only [hKi, Bool.false_eq_true, ↓reduceIte, List.foldl_nil] at this ⊢
      exact this

theorem cutInv_nil (K : Rev → Bool) : CutInv K [] [] := by
  refine ⟨List.Pairwise.nil, fun k => Or.inl ⟨rfl, fun r hr => ?_⟩⟩
  simp [kiOfKey, kiRevs, kiEmpty, Gen.empty] at hr

theorem idxRestore_eq_foldl (ents : List KvEnt) : idxRestore ents = ents.foldl idxRestoreEnt [] := rfl

/-- **The whole bucket, its surviving entries rebuilt** (`K`: the surviving revisions, a suffix of
each key's): the invariant. -/
theorem cutInv_logEnts (K : Rev → Bool) : ∀ (rl : List (List Change)), rl.length < 2 ^ 63 →
    (∀ cs ∈ rl, cs.length < 2 ^ 63) → LogWf' rl.reverse →
    (∀ e₁ ∈ evsOf rl.reverse, ∀ e₂ ∈ evsOf rl.reverse,
      e₁.key = e₂.key → Rev.lt e₁.rev e₂.rev → K e₁.rev = true → K e₂.rev = true) →
    CutInv K (evsOf rl.reverse)
      (idxRestore ((logEnts rl.reverse 0 rl.reverse.length).filter (fun e => K e.rev)))
  | [], _, _, _, _ => by
    simpa [logEnts, idxRestore, evsOf] using cutInv_nil K
  | cs :: rl, hlen, hcs, hwf, hK => by
    rw [List.reverse_cons] at hwf hK ⊢
    have hl : rl.reverse.length + 1 < 2 ^ 63 := by simp at hlen ⊢; omega
    have hcs1 : cs.length < 2 ^ 63 := hcs cs List.mem_cons_self
    have hcsl : ∀ c ∈ rl.reverse, c.length < 2 ^ 63 :=
      fun c hc => hcs c (List.mem_cons_of_mem _ (List.mem_reverse.1 hc))
    rw [evsOf_append] at hK
    have ih := cutInv_logEnts K rl (by simp at hlen; omega)
      (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hwf.prefix
      (fun e₁ h₁ e₂ h₂ => hK e₁ (List.mem_append_left _ h₁) e₂ (List.mem_append_left _ h₂))
    rw [List.length_append, List.length_singleton, logEnts_snoc, evsOf_append, List.filter_append]
    rw [idxRestore_eq_foldl] at ih ⊢
    rw [List.foldl_append]
    by_cases hne : rl.reverse = []
    · -- the first revision: no change (`LogWf'`)
      have hnil : cs = [] := by
        have h0 := hwf.1 (by simp)
        rw [hne] at h0
        simpa using h0
      subst hnil
      simpa [entsOfRev, evsOfRev] using ih
    · rw [stateAt_append_lt _ cs (by have := List.length_pos_iff.2 hne; omega), stateAt_last,
        entsOfRev_range]
      have h := cutInv_rev hl hcs1 hcsl hwf hne K hK ih cs.length (Nat.le_refl _)
      rw [List.take_length] at h
      exact h

/-! ## The level: every dropped revision deletable at `c` -/

/-- A key index whose every revision is at or below `c` and none kept by compaction at `c`: the
compaction empties it. -/
theorem kiCompact_empty_of_dropped {ki : KeyIndex} (hwf : KiWf ki) (c : w64)
    (hall : ∀ r ∈ kiRevs ki, sint.Z r.main ≤ sint.Z c) (hav : kiAvail c ki = none) :
    kiIsEmpty (kiCompact c ki) = true := by
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  have hgm : ki.gens.getD (compactGenIdx c ki.gens) Gen.empty ∈ ki.gens := by
    rw [getD_lt _ hlt]; exact List.getElem_mem hlt
  have hw : genWalk (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs (pAbove c) = -1 := by
    unfold kiAvail at hav
    simp only [] at hav
    split at hav
    · assumption
    · cases hav
  have hempty : (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs = [] := by
    rcases genWalk_pAbove_spec (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs c with
      ⟨-, hgt⟩ | ⟨j, hj, h1, -⟩
    · cases hr : (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs with
      | nil => rfl
      | cons r rs =>
        have hrm : r ∈ (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs := by rw [hr]; simp
        have := hgt r hrm
        have := hall r (kiRevs_mem hgm hrm)
        omega
    · rw [hw] at h1; omega
  have hlast : compactGenIdx c ki.gens + 1 = ki.gens.length := by
    by_cases h : compactGenIdx c ki.gens + 1 < ki.gens.length
    · exact absurd hempty (hwf.nonlast _ h)
    · omega
  rw [kiIsEmpty_eq, kiCompact_gens, dropSet_length]
  simp only [decide_eq_true_eq]
  refine ⟨by omega, ?_⟩
  have hne' : ((ki.gens.set (compactGenIdx c ki.gens) (cutGen c (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty))).drop
      (compactGenIdx c ki.gens)) ≠ [] := by
    intro h; have := congrArg List.length h; rw [dropSet_length] at this; simp at this; omega
  rw [getLastD_eq_getD _ _ hne', dropSet_length, show ki.gens.length - compactGenIdx c ki.gens - 1 = 0 by omega,
    dropSet_getD0 _ _ _ _ hlt]
  exact (cutGen_revs_ne c _).2 hempty

/-- **The cut is at or before what compaction at `c` keeps** when every revision before it is at
or below `c` and not the one compaction at `c` keeps. -/
theorem cutLe_of_dropped {ki : KeyIndex} (hwf : KiWf ki) (c : w64) {gi j : Nat}
    (hgi : gi < ki.gens.length) (hj : j < (ki.gens.getD gi Gen.empty).revs.length)
    (hbef : ∀ r, RevBefore ki gi j r → sint.Z r.main ≤ sint.Z c ∧ kiAvail c ki ≠ some r) :
    CutLe c ki gi j := by
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  by_cases h1 : gi < compactGenIdx c ki.gens
  · exact Or.inl ⟨h1, hj⟩
  · right
    generalize hgc : compactGenIdx c ki.gens = gc at *
    by_cases hge : (ki.gens.getD gc Gen.empty).revs = []
    · -- an empty generation `doCompact` stops at is the last
      have hlast : gc + 1 = ki.gens.length := by
        by_cases h : gc + 1 < ki.gens.length
        · exact absurd hge (hwf.nonlast _ h)
        · omega
      have : gi = gc := by omega
      subst this
      rw [hge] at hj; simp at hj
    · have hcr := cmpRevIdx_lt c ki (by rw [hgc]; exact hge)
      rw [hgc] at hcr
      by_cases hok : gi = gc ∧ j ≤ cmpRevIdx c ki
      · exact hok
      · exfalso
        -- the revision compaction at `c` looks at is before the cut
        have hb : RevBefore ki gi j (revAt ki gc (cmpRevIdx c ki)) := by
          refine ⟨gc, cmpRevIdx c ki, ?_, hlt, hcr, rfl⟩
          by_cases hg : gc < gi
          · exact Or.inl hg
          · right; refine ⟨by omega, ?_⟩
            have : gi = gc := by omega
            exact Nat.lt_of_not_le (fun h => hok ⟨this, h⟩)
        obtain ⟨hm, hna⟩ := hbef _ hb
        apply hna
        unfold kiAvail cmpRevIdx at *
        simp only [] at *
        rw [hgc] at *
        rcases genWalk_pAbove_spec (ki.gens.getD gc Gen.empty).revs c with ⟨hw, hgt⟩ | ⟨m, hm', hw, -, -⟩
        · exfalso
          have hmem : revAt ki gc (genWalk (ki.gens.getD gc Gen.empty).revs (pAbove c)).toNat ∈
              (ki.gens.getD gc Gen.empty).revs := by
            rw [revAt_def]
            generalize (ki.gens.getD gc Gen.empty).revs = rs at hcr ⊢
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcr]; exact List.getElem_mem hcr
          have := hgt _ hmem
          omega
        · rw [hw, ite_eq_right (by omega), revAt_def]

/-- **From the rebuild's invariant to the index invariant**, given that every dropped revision is
deletable at `c` (at or below `c`, and not one compaction at `c` keeps). -/
theorem IdxCRepN_of_cutInv (L : Log) (K : Rev → Bool) {idx : IndexM} (h : CutInv K (evsOf L) idx)
    (c : Int) (h0 : -1 ≤ c) (hc : c < 2 ^ 63)
    (hdrop : ∀ e ∈ evsOf L, K e.rev = false → sint.Z e.rev.main ≤ c ∧ ¬ keepAt L c e.rev) :
    IdxCRepN c (evsOf L) idx := by
  have hcz : sint.Z (W64 c) = c := sintZ_W64_of h0 hc
  refine ⟨h.1, fun k => ?_⟩
  have hwf := kiOfKey_wf (evsOf L) k
  have hrev : ∀ r ∈ kiRevs (kiOfKey (evsOf L) k), K r = false →
      sint.Z r.main ≤ sint.Z (W64 c) ∧ kiAvail (W64 c) (kiOfKey (evsOf L) k) ≠ some r := by
    intro r hr hK
    obtain ⟨e, he, hre, hke⟩ := kiRevs_kiOfKey hr
    obtain ⟨h1, h2⟩ := hdrop e he (by rw [hre]; exact hK)
    refine ⟨by rw [hcz, ← hre]; exact h1, fun ha => h2 ⟨k, by rw [hre]; exact ha⟩⟩
  refine ⟨c, h0, Int.le_refl _, ?_⟩
  rcases h.2 k with ⟨hg, hall⟩ | ⟨gi, j, hgi, hj, hK, hbef, hX⟩
  · refine ⟨_, _, CutLe.cmp _ _, ?_⟩
    have hE : kiIsEmpty (kiCompact (W64 c) (kiOfKey (evsOf L) k)) = true := by
      apply kiCompact_empty_of_dropped hwf _ (fun r hr => (hrev r hr (hall r hr)).1)
      cases ha : kiAvail (W64 c) (kiOfKey (evsOf L) k) with
      | none => rfl
      | some r =>
        have hr := kiAvail_mem ha
        exact absurd ha (hrev r hr (hall r hr)).2
    rw [hg, ← kiCompactO_eq_cutO]
    unfold kiCompactO
    rw [ite_eq_left hE]
  · refine ⟨gi, j, cutLe_of_dropped hwf _ hgi hj (fun r hb => ?_), ?_⟩
    · have hK' := hbef _ hb
      obtain ⟨i', j', -, hi', hj', rfl⟩ := hb
      exact hrev _ (revAt_mem hi' hj') hK'
    · rw [hX]
      unfold kiCutO
      rw [ite_eq_right]
      · rfl
      -- the cut keeps the key's revision at `(gi, j)`: not empty
      rw [kiIsEmpty_eq]
      simp only [decide_eq_true_eq, not_and]
      intro hl1
      have hp : CutPos (kiOfKey (evsOf L) k) gi j := ⟨hgi, Or.inl hj⟩
      rw [kiCutAt_getLastD hp]
      rw [kiCutAt_gens, dropSet_length] at hl1
      rw [ite_eq_left (by omega)]
      intro he
      rw [genDrop_revs_ne (Or.inl hj)] at he
      rw [he] at hj; simp at hj

/-! ## The bucket a compaction job thinned -/

/-- **The job's shape** (in place of round 3's `bucketThinnedAt`; review round 4, A1 (b)): the image's
`Key` entries `ents` are the log's (in order) but for, per key, a prefix of its entries, each
deletable by the compaction at `c` (`KeyDel`). A finished compaction at `c` (every deletable entry
gone), a leader's bucket mid-job (the job deletes from revision `0` up, in batches, which may stop
between two sub-revisions of one revision), and either after an earlier finished compaction
(`KeyDel` grows with `c`) all have it. -/
def entsCutAt (L : Log) (c : Int) (ents : List KvEnt) : Prop :=
  ents.Sublist (logEnts L 0 L.length) ∧
    (∀ e ∈ logEnts L 0 L.length, e ∉ ents → KeyDel L c (revBytes e.rev e.tomb)) ∧
    ∀ e₁ ∈ logEnts L 0 L.length, ∀ e₂ ∈ logEnts L 0 L.length,
      e₁.kv.key = e₂.kv.key → Rev.lt e₁.rev e₂.rev → e₂ ∉ ents → e₁ ∉ ents

/-- The whole bucket has the shape at any revision. -/
theorem entsCutAt_full (L : Log) (c : Int) : entsCutAt L c (logEnts L 0 L.length) :=
  ⟨List.Sublist.refl _, fun _ h h' => absurd h h', fun _ _ _ h₂ _ _ h => absurd h₂ h⟩

/-- Every event of the log has its entry in the bucket (same revision, key and kind). -/
theorem logEnts_of_ev {L : Log} {e : Ev} (he : e ∈ evsOf L) :
    ∃ ent ∈ logEnts L 0 L.length, ent.rev = e.rev ∧ ent.kv.key = e.key ∧ ent.tomb = e.tomb := by
  unfold evsOf at he
  rw [List.mem_flatten] at he
  obtain ⟨l, hl, hel⟩ := he
  rw [List.mem_map] at hl
  obtain ⟨⟨cs, j⟩, hp, rfl⟩ := hl
  rw [List.mem_zipIdx_iff_getElem?] at hp
  simp only at hel hp
  obtain ⟨i, hi, hrev, hch⟩ := evsOfRev_mem j cs e hel
  have hj : j < L.length := (List.getElem?_eq_some_iff.1 hp).1
  have hgd : L.getD j [] = cs := by rw [List.getD_eq_getElem?_getD, hp]; rfl
  obtain ⟨kv, hkv⟩ := changeKv_isSome (W64 j) (stateAt L (j - 1)) (stateAt_sorted L _) cs hi
  refine ⟨⟨⟨W64 j, W64 i⟩, e.change.isDel, kv⟩, ?_, hrev.symm, ?_, rfl⟩
  · rw [mem_logEnts]
    refine ⟨j, Nat.zero_le _, by omega, ?_⟩
    rw [hgd, mem_entsOfRev]
    exact ⟨i, e.change, kv, hch, hkv, rfl⟩
  · show kv.key = e.change.key
    unfold changeKv at hkv
    rw [hch] at hkv
    generalize e.change = c at hkv ⊢
    cases c with
    | put k v l => simp only at hkv; exact findKey_key hkv
    | del k => cases hkv; rfl

/-- A revision names at most one entry of the bucket. -/
theorem logEnts_rev_inj {L : Log} (hb : LogB L) {e₁ e₂ : KvEnt} (h₁ : e₁ ∈ logEnts L 0 L.length)
    (h₂ : e₂ ∈ logEnts L 0 L.length) (h : e₁.rev = e₂.rev) : e₁ = e₂ := by
  obtain ⟨j₁, i₁, c₁, kv₁, -, -, hj₁, hg₁, -, hc₁, hk₁, rfl⟩ := logEnts_entry L 0 L.length e₁ h₁
  obtain ⟨j₂, i₂, c₂, kv₂, -, -, hj₂, hg₂, -, hc₂, hk₂, rfl⟩ := logEnts_entry L 0 L.length e₂ h₂
  have hl := hb.1
  have hi₁ : i₁ < (L.getD j₁ []).length := (List.getElem?_eq_some_iff.1 hc₁).1
  have hi₂ : i₂ < (L.getD j₂ []).length := (List.getElem?_eq_some_iff.1 hc₂).1
  have hb₁ := hb.2 _ (List.mem_of_getElem? hg₁)
  have hb₂ := hb.2 _ (List.mem_of_getElem? hg₂)
  simp only [Rev.mk.injEq] at h
  have hj : j₁ = j₂ := by have := h.1; word
  subst hj
  have hi : i₁ = i₂ := by have := h.2; word
  subst hi
  rw [hc₁] at hc₂; cases hc₂
  rw [hk₁] at hk₂; cases hk₂
  rfl

/-- A sublist of a list of distinct revisions is the list filtered by its revisions. -/
theorem sublist_eq_filter_rev {l' l : List KvEnt} (hs : l'.Sublist l)
    (hp : l.Pairwise (fun a b => a.rev ≠ b.rev)) :
    l.filter (fun e => decide (∃ e' ∈ l', e'.rev = e.rev)) = l' := by
  induction hs with
  | slnil => rfl
  | cons a hs ih =>
    rw [List.pairwise_cons] at hp
    rw [List.filter_cons, ite_eq_right, ih hp.2]
    simp only [decide_eq_true_eq, not_exists, not_and]
    intro e' he' hr
    exact hp.1 e' (hs.subset he') hr.symm
  | cons_cons a hs ih =>
    rw [List.pairwise_cons] at hp
    rw [List.filter_cons, ite_eq_left (by simp)]
    congr 1
    refine Eq.trans (List.filter_congr ?_) (ih hp.2)
    intro x hx
    simp only [List.mem_cons, exists_eq_or_imp, decide_eq_decide]
    constructor
    · rintro (h | h)
      · exact absurd h (hp.1 x hx)
      · exact h
    · exact Or.inr

open Classical in
/-- **What `restoreIntoIndex` rebuilds from a bucket a compaction job thinned** (the user's decision
B1: the level at a full revision): over the job's shape at `c`, the rebuilt index is related to the
log at the full-revision level, `IdxCRepN c` — each key cut at its first surviving revision, at or
before what compaction at `c` keeps. No premise on how often a revision changes a key. -/
theorem idxRestore_cut (L : Log) (c : Int) (ents : List KvEnt) (hwf : LogWf' L) (hb : LogB L)
    (h0 : -1 ≤ c) (hc : c < L.length) (hcut : entsCutAt L c ents) :
    IdxCRepN c (evsOf L) (idxRestore ents) := by
  obtain ⟨hsub, hdel, hpre⟩ := hcut
  have hdist : (logEnts L 0 L.length).Pairwise (fun a b => a.rev ≠ b.rev) :=
    (logEnts_codes_sorted L hb.1 hb.2 0 L.length).imp (fun hlt he => by rw [he] at hlt; omega)
  let K : Rev → Bool := fun r => decide (∃ e' ∈ ents, e'.rev = r)
  have hents : (logEnts L 0 L.length).filter (fun e => K e.rev) = ents := sublist_eq_filter_rev hsub hdist
  -- an event's entry survives iff its revision does
  have hK_iff : ∀ ent ∈ logEnts L 0 L.length, K ent.rev = true ↔ ent ∈ ents := by
    intro ent hent
    simp only [K, decide_eq_true_eq]
    constructor
    · rintro ⟨e', he', hr⟩
      rw [logEnts_rev_inj hb (hsub.subset he') hent hr] at he'
      exact he'
    · intro h; exact ⟨ent, h, rfl⟩
  have hrl := cutInv_logEnts K L.reverse (by simpa using hb.1)
    (fun cs hcs => hb.2 cs (List.mem_reverse.1 hcs)) (by rw [List.reverse_reverse]; exact hwf)
  rw [List.reverse_reverse] at hrl
  have hinv := hrl (fun e₁ h₁ e₂ h₂ hk hlt hK₁ => by
    obtain ⟨ent₁, hm₁, hr₁, hk₁, -⟩ := logEnts_of_ev h₁
    obtain ⟨ent₂, hm₂, hr₂, hk₂, -⟩ := logEnts_of_ev h₂
    rw [← hr₂, hK_iff ent₂ hm₂]
    rw [← hr₁, hK_iff ent₁ hm₁] at hK₁
    by_cases hn : ent₂ ∈ ents
    · exact hn
    · exact absurd hK₁ (hpre ent₁ hm₁ ent₂ hm₂ (by rw [hk₁, hk₂, hk]) (by rw [hr₁, hr₂]; exact hlt) hn))
  rw [hents] at hinv
  apply IdxCRepN_of_cutInv L K hinv c h0 (by have := hb.1; omega)
  intro e he hKe
  obtain ⟨ent, hm, hr, -, -⟩ := logEnts_of_ev he
  have hn : ent ∉ ents := by
    intro h; rw [← hr, (hK_iff ent hm).2 h] at hKe; cases hKe
  obtain ⟨-, r, t, hrb, -, hrc, hkeep⟩ := hdel ent hm hn
  have := revBytes_rev_inj hrb
  rw [← hr, this]
  exact ⟨hrc, hkeep⟩
