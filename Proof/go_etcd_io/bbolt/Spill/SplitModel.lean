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

/-- **Every inode's share below `2 ^ 60`** (what `node.sizeLessThan`/`node.splitIndex` need so
that their running sizes do not wrap: they stop once past a bound below `2 ^ 63`). -/
def insBnd (ins : List Inode) : Prop := ∀ it ∈ ins, inSz it < 2 ^ 60

theorem insBnd_take {ins : List Inode} (h : insBnd ins) (j : Nat) : insBnd (ins.take j) :=
  fun it hit => h it (List.mem_of_mem_take hit)

theorem insBnd_drop {ins : List Inode} (h : insBnd ins) (j : Nat) : insBnd (ins.drop j) :=
  fun it hit => h it (List.mem_of_mem_drop hit)

/-- A node's size from the per-inode bound. -/
theorem insSize_le_len {ins : List Inode} (h : insBnd ins) :
    insSize ins ≤ 16 + ins.length * 2 ^ 60 := by
  induction ins with
  | nil => simp [insSize_nil]
  | cons it ins ih =>
    rw [insSize_cons]
    have h1 := h it (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

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

/-- Bytes addressable from a leaf element on the verified 64-bit architecture. -/
def leafWindow : Nat := 2 ^ 31 - 1

/-- Number of additional inodes accepted by the loop in `readableLeafPrefix`.
The first inode is always accepted so splitting a nonempty node makes progress. -/
def leafPrefixLen (i used : Nat) : List Inode → Nat
  | [] => 0
  | it :: rest =>
    if 0 < i ∧ leafWindow < used + inSz it then 0
    else 1 + leafPrefixLen (i + 1) (used + inSz it) rest

theorem leafPrefixLen_spec (l : List Inode) (i used : Nat) (hi : i ≤ 1 ∨ used ≤ leafWindow) :
    let k := leafPrefixLen i used l
    k ≤ l.length ∧ (i + k ≤ 1 ∨ used + ((l.take k).map inSz).sum ≤ leafWindow) ∧
      (i = 0 → l ≠ [] → 0 < k) := by
  induction l generalizing i used with
  | nil => simp [leafPrefixLen, hi]
  | cons it rest ih =>
    simp only [leafPrefixLen]
    split
    · rename_i h
      simp [hi, Nat.ne_of_gt h.1]
    · rename_i h
      have hnext : i + 1 ≤ 1 ∨ used + inSz it ≤ leafWindow := by omega
      obtain ⟨hlen, hfit, -⟩ := ih (i + 1) (used + inSz it) hnext
      simp only [Nat.one_add, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.length_cons]
      omega

/-- The size limit in the Go loop starts at the first element, after the
16-byte page header. A single oversized inode can occur in the loop model;
the public Put bound handles that case. -/
def leafReadable (P : List Inode) : Prop := P.length ≤ 1 ∨ insSize P ≤ 16 + leafWindow

theorem leafPrefix_fit (P : List Inode) :
    let k := leafPrefixLen 0 0 P
    k ≤ P.length ∧ leafReadable (P.take k) ∧ (P ≠ [] → 0 < k) := by
  obtain ⟨hk, hfit, hpos⟩ := leafPrefixLen_spec P 0 0 (Or.inl (by omega))
  refine ⟨hk, ?_, hpos rfl⟩
  simp only [leafReadable, List.length_take, Nat.min_eq_left hk, insSize_eq]
  omega

theorem pieceFits_take {ps : Nat} {P : List Inode} (h : pieceFits ps P) (k : Nat) :
    pieceFits ps (P.take k) := by
  rcases h with h | h
  · left; simp; omega
  · right; exact Nat.le_trans (insSize_take_le P k) h

/-- A normal fill-factor cut, prior to enforcing the leaf element address limit. -/
def splitCandidate (ps : Nat) (P : List Inode) (k : Nat) : Prop :=
  k ≤ P.length ∧ (k = P.length ∨ 2 ≤ k ∧ k + 3 ≤ P.length) ∧ pieceFits ps (P.take k)

def pieceFitFor (leaf : Bool) (ps : Nat) (P : List Inode) : Prop :=
  pieceFits ps P ∧ (leaf = true → leafReadable P)

def pieceMin (leaf : Bool) : Nat := if leaf then 1 else 2

def remainderMin (leaf : Bool) : Nat := if leaf then 1 else 3

/-- The final split index. The branch case preserves the usual minimum child
count. A leaf can split down to a singleton when its values require it. -/
theorem splitCandidate_final (leaf : Bool) (ps : Nat) (P : List Inode) (k : Nat)
    (hk : splitCandidate ps P k) :
    let j := if leaf then leafPrefixLen 0 0 (P.take k) else k
    j ≤ P.length ∧ pieceFitFor leaf ps (P.take j) ∧
      (j ≠ P.length → pieceMin leaf ≤ j ∧ j + remainderMin leaf ≤ P.length) := by
  obtain ⟨hle, hcount, hpiece⟩ := hk
  cases leaf with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pieceFitFor, false_implies, and_true,
      pieceMin, remainderMin]
    exact ⟨hle, hpiece, fun h => hcount.resolve_left h⟩
  | true =>
    simp only [↓reduceIte, pieceFitFor, true_implies, pieceMin, remainderMin]
    let j := leafPrefixLen 0 0 (P.take k)
    obtain ⟨hj, hr, hp⟩ := leafPrefix_fit (P.take k)
    change j ≤ _ at hj
    have hjk : j ≤ k := by simpa [Nat.min_eq_left hle] using hj
    have htake : (P.take k).take j = P.take j := by rw [List.take_take, Nat.min_eq_left hjk]
    change leafReadable ((P.take k).take j) at hr
    rw [htake] at hr
    have hf := pieceFits_take hpiece j
    rw [htake] at hf
    refine ⟨by omega, ⟨hf, hr⟩, fun hne => ⟨?_, by omega⟩⟩
    apply hp
    intro he
    have hzero := congrArg List.length he
    simp [Nat.min_eq_left hle] at hzero
    omega

/-- At most four branch separators are kept on an unsplit page. Each child
entry fits its share of the address window. -/
theorem branchPiece_readable (P : List Inode) (h : pieceFits 4096 P)
    (hb : ∀ it ∈ P, it.key'.len.toNat + it.value'.len.toNat ≤ branchKeyMax) :
    leafReadable P := by
  right
  rcases h with h | h
  · have sumBound (Q : List Inode)
          (hq : ∀ it ∈ Q, it.key'.len.toNat + it.value'.len.toNat ≤ branchKeyMax) :
          (Q.map inSz).sum ≤ Q.length * (16 + branchKeyMax) := by
      induction Q with
      | nil => simp
      | cons it Q ih =>
        have hi := hq it (by simp)
        have ht := ih (fun q h => hq q (by simp [h]))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, inSz]
        omega
    have hsum := sumBound P hb
    have hfour := Nat.mul_le_mul_right (16 + branchKeyMax) h
    rw [insSize_eq]
    unfold branchKeyMax at hsum hfour
    unfold leafWindow
    omega
  · unfold leafWindow; omega

/-- The element count fits its 16-bit field. The complete page's byte count
includes the header that precedes the first element's address window. -/
theorem pieceFits_bounds (ps : Nat) (P : List Inode) (hps : ps < 2 ^ 20)
    (hE : ∀ it ∈ P, it.key'.len.toNat + it.value'.len.toNat ≤ bboltEntryMax)
    (h : pieceFits ps P) (hr : leafReadable P) :
    P.length < 0xFFFF ∧ insSize P ≤ 16 + leafWindow := by
  have hl := insSize_ge_len P
  constructor
  · rcases h with h | h <;> omega
  rcases hr with h1 | h1
  · cases P with
    | nil => simp [insSize_nil, leafWindow]
    | cons it rest =>
      have hlen : rest.length + 1 ≤ 1 := h1
      have hrest : rest = [] := List.length_eq_zero_iff.mp (by omega)
      subst rest
      have he := hE it (by simp)
      simp only [insSize_cons, insSize_nil, inSz, leafWindow]
      unfold bboltEntryMax at he
      omega
  · exact h1

end model

end bbolt
end EtcdGrove
end Perennial
