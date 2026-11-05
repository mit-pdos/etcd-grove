/-
The public reader cursor triples' (U6h, `notes/bbolt-proof-plan.md`) positions for the moves to the
end (`last`, used by `Last` and `prev`): the descent by last children (`rTlF`, the top element
about to descend, landing just before the position `s`), and the B+tree keys along a reader's
stack (`rKeysAt`: `treeKeys` at a stored bucket's page, whose children are not empty: a reader's
tree has no empty non-root leaf).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Pos

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pubRPos
variable [GooseExts]
variable {v : View} {bv : List w8} {pp : Loc}

/-- **The top element `e` of a stack about to descend by last children** (`last`) at position
`pid` (fuel `m`), landing on the entry just before `s` (of the entries below it): a branch at
index `j` (`s` the entries below its children up to `j`), or a leaf on its entry `s - 1`. -/
def rTlF (v : View) (bv : List w8) (pp : Loc) (m pid : Nat) (e : elemRef) (s : Nat) : Prop :=
  (∃ pg j, rBrAt v bv pp pid e pg j ∧ s = entsBefore v.pages (m - 1) pg (j + 1)) ∨
  (∃ pg i, rLfAt v bv pp pid e pg i ∧ i < pageCount pg ∧ s = i + 1)

/-- The top element `e` refers to a leaf page at position `pid`, at any index. -/
def rLfTop (v : View) (bv : List w8) (pp : Loc) (pid : Nat) (e : elemRef) : Prop :=
  ∃ pg, rPageAt v bv pp pid = some (e.page', pg) ∧ e.node' = null ∧ pageFlags pg = leafPageFlag

/-- Position `pid` of a reader bucket has B+tree keys (an inline bucket: its only leaf). -/
def rKeysAt (v : View) (bv : List w8) (pid : Nat) : Prop :=
  inBucketRoot bv = 0 ∨ ∃ lo hi, treeKeys v.pages pid lo hi

theorem rKeys_root (hok : rBktOK v bv) : rKeysAt v bv (inBucketRoot bv) := by
  by_cases hi : inBucketRoot bv = 0
  · exact Or.inl hi
  · exact Or.inr ⟨none, none, hok.2.2 hi⟩

/-- **A branch's child has keys and is not empty.** -/
theorem rKeys_child {pid : Nat} {e : elemRef} {pg : List w8} {j : Nat} (hk : rKeysAt v bv pid)
    (hbr : rBrAt v bv pp pid e pg j) :
    rKeysAt v bv (branchPgid pg j) ∧
      ∃ cpg, v.pages !! branchPgid pg j = some cpg ∧ 0 < pageCount cpg := by
  obtain ⟨hib, hpa, -, hfl, hj, -⟩ := hbr
  rcases hk with h | ⟨lo, hi, hk⟩
  · exact absurd h hib
  have hpv := (rPageAt_tree v bv pp pid _ pg hib hpa).1
  cases hk with
  | leaf _ pg' _ _ hpg' hfl' _ _ =>
    rw [hpv] at hpg'; cases hpg'; rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
  | branch _ pg' _ _ kind hpg' _ _ _ hne hch =>
    rw [hpv] at hpg'; cases hpg'
    obtain ⟨cpg, hc, hc0, -, -⟩ := hne j hj
    exact ⟨Or.inr ⟨_, _, hch j hj⟩, cpg, hc, hc0⟩

/-- The keys along a stack prefix. -/
theorem rPreF_keys : ∀ (A : List elemRef) (n pid m pid' o : Nat), rPreF v bv pp n pid A m pid' o →
    rKeysAt v bv pid → rKeysAt v bv pid'
  | [], _, _, _, _, _, h, hk => by
    simp only [rPreF] at h; obtain ⟨-, rfl, -⟩ := h; exact hk
  | _ :: A, _, _, _, _, _, ⟨_, _, _, _, _, hbr, hp, _⟩, hk =>
    rPreF_keys A _ _ _ _ _ hp (rKeys_child hk hbr).1

/-- A child of a branch position with keys, read through `rPageAt`, is not empty. -/
theorem rKeys_child_pg {pid : Nat} {e : elemRef} {pg : List w8} {j : Nat} {l : Loc}
    {pgc : List w8} (hk : rKeysAt v bv pid) (hbr : rBrAt v bv pp pid e pg j)
    (hpa : rPageAt v bv pp (branchPgid pg j) = some (l, pgc)) : 0 < pageCount pgc := by
  obtain ⟨-, cpg, hc, hc0⟩ := rKeys_child hk hbr
  have := (rPageAt_tree v bv pp _ l pgc hbr.1 hpa).1
  rw [hc] at this; cases this; exact hc0

/-- **The last descent's end**: a leaf on top of a prefix, on an entry. -/
theorem rTlF_leaf (A : List elemRef) (m pid o : Nat) (e : elemRef) (pg : List w8) (i : Nat)
    (hp : rPreF v bv pp (rFuel v bv) (inBucketRoot bv) A m pid o) (hm : 0 < m)
    (hlf : rLfAt v bv pp pid e pg i) (hi : i < pageCount pg) :
    rPosAt v bv pp (A ++ [e]) (o + i) (o + i + 1) := by
  have h := rHdF_leaf A m pid o i e pg hp hm hlf
  rw [if_pos hi] at h; exact h

/-- **The last descent's step**: a branch on top of a prefix extends it, its child's last
element (at index `count - 1`) landing just before the same position. -/
theorem rTlF_down (A : List elemRef) (m pid o s : Nat) (e e' : elemRef) (pg pgc : List w8) (j : Nat)
    (hp : rPreF v bv pp (rFuel v bv) (inBucketRoot bv) A m pid o) (hm : 1 < m)
    (hbr : rBrAt v bv pp pid e pg j) (hs : s = entsBefore v.pages (m - 1) pg (j + 1))
    (hpa : rPageAt v bv pp (branchPgid pg j) = some (e'.page', pgc)) (hn : e'.node' = null)
    (hc : 0 < pageCount pgc) (hidx : e'.index' = W64 ((pageCount pgc : Int) - 1))
    (hfl : pageFlags pgc = branchPageFlag ∨ pageFlags pgc = leafPageFlag) :
    rPreF v bv pp (rFuel v bv) (inBucketRoot bv) (A ++ [e]) (m - 1) (branchPgid pg j)
        (o + entsBefore v.pages (m - 1) pg j) ∧
      ∃ s', rTlF v bv pp (m - 1) (branchPgid pg j) e' s' ∧
        o + entsBefore v.pages (m - 1) pg j + s' = o + s := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  simp only [show m' + 2 - 1 = m' + 1 by omega] at hs ⊢
  refine ⟨rPreF_snoc A _ _ (m' + 1) pid o e pg j hp hbr, ?_⟩
  have hidx' : e'.index' = W64 (((pageCount pgc - 1 : Nat) : Int)) := by
    rw [hidx]; congr 1; omega
  have hsucc := entsBefore_succ v.pages (m' + 1) pg j
  rcases hfl with hfl | hfl
  · refine ⟨entsBefore v.pages m' pgc (pageCount pgc), Or.inl ⟨pgc, pageCount pgc - 1,
      ⟨hbr.1, hpa, hn, hfl, by omega, hidx'⟩, by rw [Nat.sub_add_cancel hc]; rfl⟩, ?_⟩
    rw [hs, hsucc, ← rLeaves_tree v bv _ _ hbr.1,
      rLeaves_branch v bv pp m' _ _ pgc hbr.1 hpa hfl]
    unfold entsBefore; omega
  · refine ⟨pageCount pgc, Or.inr ⟨pgc, pageCount pgc - 1,
      ⟨hpa, hn, hfl, by omega, hidx'⟩, by omega, by omega⟩, ?_⟩
    rw [hs, hsucc, ← rLeaves_tree v bv _ _ hbr.1, rLeaves_leaf v bv pp m' _ _ pgc hpa hfl,
      entCount_single, Nat.add_assoc]

/-! ### `prev`'s moves -/

/-- **A stack whose indices are all at most `0` is at position `0`.** -/
theorem rPosF_zero : ∀ (n pid : Nat) (B : List elemRef) (i s : Nat), rPosF v bv pp n pid B i s →
    (∀ e ∈ B, sint.Z e.index' ≤ 0) → i = 0
  | 0, _, _, _, _, h, _ => absurd h (by simp [rPosF])
  | _ + 1, _, [], _, _, h, _ => absurd h (by simp [rPosF])
  | _ + 1, _, [e], i, s, ⟨pg, hlf, _⟩, hz => by
    have h := hz e (by simp)
    have := hlf.2.2.2.1; have := pageCount_lt pg
    rw [hlf.2.2.2.2] at h
    have : sint.Z (W64 (i : Int)) = i := by word
    omega
  | n + 1, _, e :: e' :: es, i, s, ⟨pg, j, i', s', hbr, hr, hi, _⟩, hz => by
    have h := hz e (by simp)
    have := hbr.2.2.2.2.1; have := pageCount_lt pg
    rw [hbr.2.2.2.2.2] at h
    have hj : j = 0 := by
      have : sint.Z (W64 (j : Int)) = j := by word
      omega
    have := rPosF_zero n _ _ _ _ hr (fun x hx => hz x (List.mem_cons_of_mem _ hx))
    rw [hi, hj, entsBefore_zero, this]

/-- **`prev`'s move at element `k`** (its index above `0`, every element above it at `0`): the
stack up to it, its index one less, is about to descend by last children to just before the old
position `i`. -/
theorem rPrev_found (els : List elemRef) (i s k : Nat) (hpos : rPosAt v bv pp els i s)
    (hk : k < els.length) (hz : ∀ e ∈ els.drop (k + 1), sint.Z e.index' ≤ 0)
    (hgt : 0 < sint.Z els[k].index') :
    ∃ m pid o s', rPreF v bv pp (rFuel v bv) (inBucketRoot bv) (els.take k) m pid o ∧ 0 < m ∧
      rTlF v bv pp m pid { els[k] with index' := els[k].index' - W64 1 } s' ∧ o + s' = i := by
  have hsplit : els = els.take k ++ els[k] :: els.drop (k + 1) := by simp
  unfold rPosAt at hpos
  rw [hsplit] at hpos
  obtain ⟨m, pid, o, i', s', pg, hp, hr, hi, -, -, -⟩ := rPosF_top _ _ _ _ _ _ _ hpos
  match m, hrest : els.drop (k + 1), hr with
  | 0, _, hr => exact absurd hr (by simp [rPosF])
  | m + 1, [], ⟨pg2, hlf, _⟩ =>
    have := hlf.2.2.2.1; have := pageCount_lt pg2
    have hix : sint.Z els[k].index' = (i' : Int) := by rw [hlf.2.2.2.2]; word
    refine ⟨m + 1, pid, o, i', hp, by omega, Or.inr ⟨pg2, i' - 1,
      ⟨hlf.1, hlf.2.1, hlf.2.2.1, by omega, ?_⟩, by omega, by omega⟩, by omega⟩
    show els[k].index' - W64 1 = W64 (((i' - 1 : Nat) : Int))
    rw [hlf.2.2.2.2]
    have : ((i' - 1 : Nat) : Int) = (i' : Int) - 1 := by omega
    rw [this]; word
  | m + 1, e' :: es, ⟨pg2, j, i2, s2, hbr, hr2, hi2, _⟩ =>
    have := hbr.2.2.2.2.1; have := pageCount_lt pg2
    have hix : sint.Z els[k].index' = (j : Int) := by rw [hbr.2.2.2.2.2]; word
    have hz' : ∀ e ∈ e' :: es, sint.Z e.index' ≤ 0 := by rw [← hrest]; exact hz
    have h0 := rPosF_zero m _ _ _ _ hr2 hz'
    refine ⟨m + 1, pid, o, entsBefore v.pages m pg2 j, hp, by omega, Or.inl ⟨pg2, j - 1,
      ⟨hbr.1, hbr.2.1, hbr.2.2.1, hbr.2.2.2.1, by omega, ?_⟩, ?_⟩, by omega⟩
    · show els[k].index' - W64 1 = W64 (((j - 1 : Nat) : Int))
      rw [hbr.2.2.2.2.2]
      have : ((j - 1 : Nat) : Int) = (j : Int) - 1 := by omega
      rw [this]; word
    · simp only [Nat.add_sub_cancel]; congr 1; omega

end pubRPos

end bbolt
end EtcdGrove
end Perennial
