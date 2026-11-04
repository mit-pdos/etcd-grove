/-
The pure model of `node.sizeLessThan`, `node.splitIndex` and of the pieces `node.splitTwo` and
`node.split` make (U9a, `notes/bbolt-proof-plan.md`), with the fit lemma: every piece is at most
four inodes or within the page size (`pieceFits`), so that a page of `bboltEntryMax`-bounded
entries satisfies `node.write`'s premises (`pieceFits_bounds`). Ported from the old proof's
`NodeModel`/`SpillFit` (`old/bbolt/`), in `Nat` (the specs assume `insSize ins < 2 ^ 63`, so the
`uintptr` sums do not wrap).
-/
module

public import Proof.go_etcd_io.bbolt.Model.WOps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section model
variable [GooseExts]

/-- An inode's share of a page: its element and its key's and value's bytes. -/
def inSz (it : Inode) : Nat := 16 + it.key'.len.toNat + it.value'.len.toNat

theorem insSize_eq (ins : List Inode) : insSize ins = 16 + (ins.map inSz).sum := rfl

theorem insSize_nil : insSize ([] : List Inode) = 16 := rfl

theorem insSize_cons (it : Inode) (ins : List Inode) :
    insSize (it :: ins) = insSize ins + inSz it := by
  simp only [insSize_eq, List.map_cons, List.sum_cons]; omega

theorem insSize_snoc (ins : List Inode) (it : Inode) :
    insSize (ins ++ [it]) = insSize ins + inSz it := by
  simp only [insSize_eq, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]; omega

theorem insSize_append (A B : List Inode) :
    insSize (A ++ B) + 16 = insSize A + insSize B := by
  simp only [insSize_eq, List.map_append, List.sum_append]; omega

theorem insSize_take_le (ins : List Inode) (j : Nat) : insSize (ins.take j) ≤ insSize ins := by
  have h := insSize_append (ins.take j) (ins.drop j)
  rw [List.take_append_drop] at h
  have : 16 ≤ insSize (ins.drop j) := by rw [insSize_eq]; omega
  omega

theorem insSize_drop_le (ins : List Inode) (j : Nat) : insSize (ins.drop j) ≤ insSize ins := by
  have h := insSize_append (ins.take j) (ins.drop j)
  rw [List.take_append_drop] at h
  have : 16 ≤ insSize (ins.take j) := by rw [insSize_eq]; omega
  omega

theorem insSize_take_mono (ins : List Inode) (a b : Nat) (h : a ≤ b) :
    insSize (ins.take a) ≤ insSize (ins.take b) := by
  have e : ins.take a = (ins.take b).take a := by rw [List.take_take, Nat.min_eq_left h]
  rw [e]; exact insSize_take_le _ _

theorem insSize_ge_len (ins : List Inode) : 16 + 16 * ins.length ≤ insSize ins := by
  induction ins with
  | nil => simp [insSize_nil]
  | cons it ins ih => rw [insSize_cons]; simp only [inSz, List.length_cons]; omega

/-- **`node.splitIndex`'s loop** from index `i` (last index `idx`, size `sz`) over the inodes `l`
left to it: the first inode from the third on whose element takes the size past `t` is the split
index, else the last one the loop reaches. -/
def splitGo (t : Nat) : Nat → Nat → Nat → List Inode → Nat × Nat
  | _, idx, sz, [] => (idx, sz)
  | i, _, sz, it :: rest =>
    if 2 ≤ i ∧ t < sz + inSz it then (i, sz) else splitGo t (i + 1) i (sz + inSz it) rest

/-- **`n.splitIndex(t)`**: the index and the size the loop ends with; it leaves the last
`MinKeysPerPage = 2` inodes out. -/
def splitIdx (t : Nat) (ins : List Inode) : Nat × Nat :=
  splitGo t 0 0 16 (ins.take (ins.length - 2))

/-- The invariant of `splitGo`: the result's index `k`, if it is at least 3, has its first `k`
inodes within `t`; and `k` is at least 2 and leaves three inodes when the loop got to index 2. -/
private theorem splitGo_spec (t : Nat) (ins : List Inode) (L : Nat) (hL : L ≤ ins.length) :
    ∀ (n i idx sz : Nat), n + i = L → sz = insSize (ins.take i) →
      (idx + 1 = i ∨ (i = 0 ∧ idx = 0)) →
      (∀ j, 3 ≤ j → j ≤ i → insSize (ins.take j) ≤ t) →
      let r := splitGo t i idx sz ((ins.take L).drop i)
      (3 ≤ r.1 → insSize (ins.take r.1) ≤ t) ∧ (3 ≤ L → 2 ≤ r.1 ∧ r.1 + 1 ≤ L) := by
  intro n
  induction n with
  | zero =>
    intro i idx sz hn hsz hidx hprev
    have hi : i = L := by omega
    subst hi
    have : (ins.take i).drop i = [] := by simp
    simp only [this, splitGo]
    refine ⟨fun h3 => hprev idx h3 (by omega), fun h3 => by omega⟩
  | succ n ih =>
    intro i idx sz hn hsz hidx hprev
    have hiL : i < (ins.take L).length := by simp; omega
    have hdrop : (ins.take L).drop i = (ins.take L)[i] :: (ins.take L).drop (i + 1) :=
      List.drop_eq_getElem_cons hiL
    have hget : (ins.take L)[i] = ins[i]'(by omega) := by simp
    rw [hdrop]
    simp only [splitGo]
    have htake : insSize (ins.take (i + 1)) = sz + inSz (ins[i]'(by omega)) := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some]; rw [insSize_snoc, hsz]
    split
    · rename_i hb
      refine ⟨fun h3 => hprev i h3 (by omega), fun _ => ⟨hb.1, by omega⟩⟩
    · rename_i hb
      have := ih (i + 1) i (sz + inSz ((ins.take L)[i])) (by omega)
        (by rw [htake, hget]) (Or.inl rfl)
        (by
          intro j h3 hj
          rcases Nat.lt_or_ge j (i + 1) with hj' | hj'
          · exact hprev j h3 (by omega)
          · have : j = i + 1 := by omega
            subst this
            rw [htake, ← hget]
            have : ¬ (2 ≤ i ∧ t < sz + inSz ((ins.take L)[i])) := hb
            omega)
      exact this

/-- **`splitIdx`'s index** on a node of at least five inodes: at least 2, three inodes left after
it, and its first part within `t` from three inodes on. -/
theorem splitIdx_spec (t : Nat) (ins : List Inode) (h5 : 5 ≤ ins.length) :
    2 ≤ (splitIdx t ins).1 ∧ (splitIdx t ins).1 + 3 ≤ ins.length ∧
      (3 ≤ (splitIdx t ins).1 → insSize (ins.take (splitIdx t ins).1) ≤ t) := by
  have := splitGo_spec t ins (ins.length - 2) (by omega) (ins.length - 2) 0 0 16 (by omega)
    (by simp [insSize_nil]) (Or.inr ⟨rfl, rfl⟩) (fun j h3 hj => by omega)
  simp only [List.drop_zero] at this
  unfold splitIdx
  exact ⟨(this.2 (by omega)).1, by have := (this.2 (by omega)).2; omega, this.1⟩

/-- **A piece of a split fits a page**: at most four inodes (`2 * MinKeysPerPage`, which
`splitTwo` never splits), or its page within the page size `ps`. -/
def pieceFits (ps : Nat) (P : List Inode) : Prop := P.length ≤ 4 ∨ insSize P ≤ ps

/-- An unsplit node (`splitTwo` returns `nil`: four inodes or fewer, or `sizeLessThan(ps)`). -/
theorem pieceFits_unsplit (ps : Nat) (ins : List Inode)
    (h : ins.length ≤ 4 ∨ ins = [] ∨ insSize ins < ps) : pieceFits ps ins := by
  unfold pieceFits
  rcases h with h | h | h
  · exact Or.inl h
  · subst h; exact Or.inl (by simp)
  · exact Or.inr (by omega)

/-- The first piece of a split at `splitIdx t ins` with `t ≤ ps`. -/
theorem pieceFits_split (t ps : Nat) (ins : List Inode) (h5 : 5 ≤ ins.length) (ht : t ≤ ps) :
    pieceFits ps (ins.take (splitIdx t ins).1) := by
  obtain ⟨h2, h3, hs⟩ := splitIdx_spec t ins h5
  unfold pieceFits
  rcases Nat.lt_or_ge (splitIdx t ins).1 3 with hk | hk
  · left; simp; omega
  · right; have := hs hk; omega

/-- **What `node.write` needs of a piece**: with the page size below `2 ^ 20` and every inode's
key and value within `bboltEntryMax`, a fitting piece has fewer than `0xFFFF` inodes and a
page below `2 ^ 31 - 1` (`MaxAllocSize`). -/
theorem pieceFits_bounds (ps : Nat) (P : List Inode) (hps : ps < 2 ^ 20)
    (hE : ∀ it ∈ P, it.key'.len.toNat + it.value'.len.toNat ≤ bboltEntryMax)
    (h : pieceFits ps P) :
    P.length < 0xFFFF ∧ insSize P < 2 ^ 31 - 1 := by
  have hl := insSize_ge_len P
  rcases h with h | h
  · have hsum : ∀ (Q : List Inode), (∀ it ∈ Q, it.key'.len.toNat + it.value'.len.toNat ≤ bboltEntryMax) →
        (Q.map inSz).sum ≤ Q.length * (16 + bboltEntryMax) := by
      intro Q hQ
      induction Q with
      | nil => simp
      | cons it Q ih =>
        have h1 := hQ it (by simp)
        have h2 := ih (fun x hx => hQ x (by simp [hx]))
        have h3 : inSz it ≤ 16 + bboltEntryMax := by unfold inSz; omega
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
        omega
    have h1 := hsum P hE
    rw [insSize_eq]
    have : P.length * (16 + bboltEntryMax) ≤ 4 * (16 + bboltEntryMax) :=
      Nat.mul_le_mul_right _ h
    unfold bboltEntryMax at this h1
    omega
  · omega

end model

end bbolt
end EtcdGrove
end Perennial
