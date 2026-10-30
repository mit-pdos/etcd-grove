/-
The parts `n.split` makes fit a page write (`node.write`'s conditions: fewer than 65535 inodes,
the layout below `MaxAllocSize`), when the split threshold is at most the page size (a fact of
float arithmetic: `splitThr`, for a fill percent clamped to [0.1, 1]), the page size at most
1 MiB, and every inode's key and value together at most 2^28 bytes (`split_fit`).

Without such bounds bbolt fails: a leaf of at most four inodes is never split, and
`WriteInodeToPage` writes each element's position as a `uint32` (four values of 2^30 bytes
wrap it) and slices the page through a `[MaxAllocSize]byte` array (one value of
`MaxValueSize` with a key of two bytes or more panics).
-/
module

public import Spec.go_etcd_io.bbolt.node__split_x

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]
variable [go.FloatConvSemantics]

/-- The bytes of an inode's key and value. -/
def inodeKV (it : Inode) : Nat := uint.nat it.key'.len + uint.nat it.value'.len

/-- A part's layout. -/
def layoutOf (ins : List Inode) : Nat := 16 + 16 * ins.length + (ins.map inodeKV).sum

theorem layoutOf_snoc (pre : List Inode) (it : Inode) :
    layoutOf (pre ++ [it]) = layoutOf pre + 16 + inodeKV it := by
  unfold layoutOf; simp; omega

theorem layoutOf_ge (pre : List Inode) : 16 + 16 * pre.length ≤ layoutOf pre := by
  unfold layoutOf; omega

theorem layoutOf_append (A B : List Inode) :
    layoutOf (A ++ B) = layoutOf A + 16 * B.length + (B.map inodeKV).sum := by
  unfold layoutOf; simp; omega

theorem layoutOf_take_le (L : List Inode) (a b : Nat) (h : a ≤ b) :
    layoutOf (L.take a) ≤ layoutOf (L.take b) := by
  have e : L.take b = L.take a ++ (L.drop a).take (b - a) := by
    rw [show b = a + (b - a) by omega, List.take_add]; simp
  rw [e, layoutOf_append]; omega

theorem el_add (sz : w64) (it : Inode) (S : Nat) (hs : uint.nat sz = S) (hS : S ≤ 2 ^ 30)
    (hk : inodeKV it ≤ 2 ^ 28) :
    uint.nat (sz + (W64 16 + it.key'.len + it.value'.len)) = S + 16 + inodeKV it := by
  unfold inodeKV at hk ⊢
  unfold uint.nat at *
  word

theorem kv_sum_le (l : List Inode) (h : ∀ it ∈ l, inodeKV it ≤ 2 ^ 28) :
    (l.map inodeKV).sum ≤ l.length * 2 ^ 28 := by
  induction l with
  | nil => simp
  | cons it rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h it (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    rw [Nat.succ_mul]; omega

/-- The split loop's result: at most two inodes, or a first part within the threshold. -/
theorem splitGo_fit (thr : w64) (hthr : uint.nat thr ≤ 2 ^ 20) (L : List Inode)
    (hel : ∀ it ∈ L, inodeKV it ≤ 2 ^ 28) :
    ∀ (l pre : List Inode) (sz : w64), pre ++ l = L → uint.nat sz = layoutOf pre →
      (3 ≤ pre.length → layoutOf pre ≤ uint.nat thr) →
      ∃ k : Nat, (splitIndexGo thr pre.length (W64 ((pre.length - 1 : Nat) : Int)) sz l).1 =
        W64 (k : Int) ∧ k ≤ L.length ∧ (k ≤ 2 ∨ layoutOf (L.take k) ≤ uint.nat thr) := by
  intro l
  induction l with
  | nil =>
    intro pre sz hL hsz hb
    simp only [List.append_nil] at hL
    subst hL
    refine ⟨pre.length - 1, rfl, by omega, ?_⟩
    by_cases h3 : pre.length ≤ 3
    · left; omega
    · right
      have := layoutOf_take_le pre (pre.length - 1) pre.length (by omega)
      rw [List.take_length] at this
      have := hb (by omega); omega
  | cons it rest ih =>
    intro pre sz hL hsz hb
    have hpel : ∀ x ∈ pre, inodeKV x ≤ 2 ^ 28 := fun x hx => hel x (by rw [← hL]; simp [hx])
    have hit : inodeKV it ≤ 2 ^ 28 := hel it (by rw [← hL]; simp)
    have hbound : layoutOf pre ≤ 2 ^ 30 := by
      by_cases h3 : 3 ≤ pre.length
      · have := hb h3; omega
      · have := kv_sum_le pre hpel
        unfold layoutOf
        have : pre.length * 2 ^ 28 ≤ 2 * 2 ^ 28 := Nat.mul_le_mul_right _ (by omega)
        omega
    have hlen : pre.length < 2 ^ 17 := by
      by_cases h3 : 3 ≤ pre.length
      · have := hb h3; have := layoutOf_ge pre; omega
      · omega
    have hsum := el_add sz it _ hsz hbound hit
    rw [← layoutOf_snoc] at hsum
    have hi : uint.Z (W64 ((pre.length : Nat) : Int)) = (pre.length : Int) := by
      have : ((pre.length : Nat) : Int) < 2 ^ 64 := by omega
      word
    have hZ : ∀ x : w64, uint.Z x = ((uint.nat x : Nat) : Int) := by intro x; unfold uint.nat; simp
    simp only [splitIndexGo]
    split
    · rename_i hc
      refine ⟨pre.length, rfl, by rw [← hL]; simp, ?_⟩
      by_cases h2 : pre.length ≤ 2
      · left; exact h2
      · right
        rw [← hL, List.take_left' rfl]
        exact hb (by omega)
    · rename_i hc
      have hle : 3 ≤ (pre ++ [it]).length → layoutOf (pre ++ [it]) ≤ uint.nat thr := by
        intro h3
        simp only [List.length_append, List.length_singleton] at h3
        rw [hi, hZ thr, hZ, hsum] at hc
        omega
      have := ih (pre ++ [it]) _ (by rw [← hL]; simp) hsum hle
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at this
      exact this

/-- A part `sizeLessThan` accepts is below the page size. -/
theorem sizeLess_fit (v : w64) (hv : uint.nat v ≤ 2 ^ 20) :
    ∀ (l : List Inode) (sz : w64) (S : Nat), uint.nat sz = S → S ≤ 2 ^ 20 →
      (∀ it ∈ l, inodeKV it ≤ 2 ^ 28) → sizeLessThanFrom (W64 16) v sz l = true →
      l = [] ∨ S + 16 * l.length + (l.map inodeKV).sum < uint.nat v := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ _; left; rfl
  | cons it rest ih =>
    intro sz S hsz hS hel h
    have hit : inodeKV it ≤ 2 ^ 28 := hel it (by simp)
    have hsum := el_add sz it S hsz (by omega) hit
    have hZ : ∀ x : w64, uint.Z x = ((uint.nat x : Nat) : Int) := by intro x; unfold uint.nat; simp
    simp only [sizeLessThanFrom] at h
    split at h
    · cases h
    · rename_i hc
      rw [hZ v, hZ, hsum] at hc
      have hlt : S + 16 + inodeKV it < uint.nat v := by omega
      right
      rcases ih _ _ hsum (by omega) (fun x hx => hel x (by simp [hx])) h with h0 | h1
      · subst h0; simp; omega
      · simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

/-- The parts fit a page write (see the module doc). -/
theorem split_fit (thr ps : w64) (hthr : uint.Z thr ≤ uint.Z ps) (hps : uint.Z ps < 2 ^ 20)
    (xs : List (Loc × node × List Inode)) (hidx : splitIdxOK thr xs) (hlast : lastFits ps xs)
    (hel : ∀ x ∈ xs, ∀ it ∈ x.2.2, inodeKV it ≤ 2 ^ 28)
    (hlen : ∀ x ∈ xs, x.2.2.length < 2 ^ 64) :
    ∀ x ∈ xs, x.2.2.length < 65535 ∧ layoutOf x.2.2 ≤ 2147483647 := by
  have hZ : ∀ x : w64, uint.Z x = ((uint.nat x : Nat) : Int) := by intro x; unfold uint.nat; simp
  rw [hZ, hZ] at hthr; rw [hZ] at hps
  have hthr' : uint.nat thr ≤ 2 ^ 20 := by omega
  intro x hx
  have hxel := hel x hx
  have hsmall : x.2.2.length ≤ 4 → x.2.2.length < 65535 ∧ layoutOf x.2.2 ≤ 2147483647 := by
    intro h4
    have := kv_sum_le x.2.2 hxel
    have : x.2.2.length * 2 ^ 28 ≤ 4 * 2 ^ 28 := Nat.mul_le_mul_right _ h4
    unfold layoutOf; omega
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  have hjl : j < xs.length := (List.getElem?_eq_some_iff.1 hj).1
  by_cases hj1 : j + 1 < xs.length
  · have hk := hidx j x hj1 hj
    have hdrop : xs.drop j = x :: xs.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hjl]
      rw [List.getElem?_eq_some_iff] at hj
      obtain ⟨_, hj⟩ := hj; rw [hj]
    rw [hdrop] at hk
    simp only [List.map_cons, List.flatten_cons] at hk
    generalize hR : x.2.2 ++ ((xs.drop (j + 1)).map (fun x => x.2.2)).flatten = R at hk
    unfold splitIndexOf at hk
    have hRel : ∀ it ∈ R, inodeKV it ≤ 2 ^ 28 := by
      intro it hit
      rw [← hR] at hit
      rcases List.mem_append.1 hit with h | h
      · exact hxel it h
      · obtain ⟨l, hl, hil⟩ := List.mem_flatten.1 h
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
        exact hel y (List.mem_of_mem_drop hy) it hil
    have hLel : ∀ it ∈ R.take (R.length - 2), inodeKV it ≤ 2 ^ 28 :=
      fun it hit => hRel it (List.mem_of_mem_take hit)
    obtain ⟨k, hk1, hk2, hk3⟩ := splitGo_fit thr hthr' (R.take (R.length - 2)) hLel
      (R.take (R.length - 2)) [] (W64 16) rfl (by unfold layoutOf uint.nat; simp) (by simp)
    simp only [List.length_nil, Nat.zero_sub] at hk1
    have h00 : W64 ((0 : Nat) : Int) = W64 0 := rfl
    rw [h00] at hk1
    rw [hk1] at hk
    have hk64 : k < 2 ^ 20 := by
      rcases hk3 with h | h
      · omega
      · have := layoutOf_ge ((R.take (R.length - 2)).take k)
        rw [List.length_take_of_le hk2] at this
        omega
    have hxl := hlen x hx
    have hke : k = x.2.2.length := by
      have : (W64 (k : Int)) = W64 (x.2.2.length : Int) := hk
      have h1 : ((k : Int)) < 2 ^ 64 := by omega
      have h2 : ((x.2.2.length : Nat) : Int) < 2 ^ 64 := by omega
      have := congrArg (fun y : w64 => y.toNat) this
      simp at this
      omega
    have htake : (R.take (R.length - 2)).take k = x.2.2 := by
      have hk2' : k ≤ R.length - 2 := by
        have := List.length_take_le (R.length - 2) R; simp only [List.length_take] at hk2; omega
      rw [List.take_take, Nat.min_eq_left hk2', ← hR, hke, List.take_left' rfl]
    rcases hk3 with h | h
    · exact hsmall (by omega)
    · rw [htake] at h
      have := layoutOf_ge x.2.2
      refine ⟨by omega, by omega⟩
  · have hlj : j + 1 = xs.length := by omega
    have hl : xs.getLast? = some x := by
      rw [List.getLast?_eq_getElem?, show xs.length - 1 = j by omega]; exact hj
    rcases hlast x hl with h | h
    · exact hsmall h
    · rcases sizeLess_fit ps (by omega) x.2.2 (W64 16) 16 (by unfold uint.nat; simp) (by omega)
        hxel h with h0 | h1
      · rw [h0]; unfold layoutOf; simp
      · unfold layoutOf; refine ⟨by omega, by omega⟩

end pure

end bbolt
end EtcdGrove
end Perennial
