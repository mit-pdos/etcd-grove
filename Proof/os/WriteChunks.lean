/-
A `pwrite` in chunks (`os.File.WriteAt`'s model, `TrustedCode/os.lean`): a write of the first `k`
bytes of the chunk `(data.drop nn).take c` at `off + nn`, over the file a write of the first `j`
bytes of `data` at `off` left (`nn ≤ j`), leaves the file a write of the first `max j (nn + k)`
bytes leaves (`pwSize_chunk`, `pwBytes_chunk`; `pwSize_pwSize` and `pwBytes_retry` of
`GooseLang/Ext/OsFs/Write.lean` are their `nn = 0`, `c = data.length` case). The chunk's write
takes the middle of the range's bytes (`osBytes_split3_range`) and gives back bytes that end where
the rest begins, or the rest is empty (`pwBytes_chunk_end`, `osBytes_app3`).
-/
module

public import GooseLang.Ext.OsFs.Write

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

theorem pwSize_chunk (sz off j nn k : Nat) (hnj : nn ≤ j) :
    pwSize (pwSize sz off j) (off + nn) k = pwSize sz off (max j (nn + k)) := by
  unfold pwSize
  by_cases hj : j = 0 <;> by_cases hk : k = 0 <;> simp [hj, hk] <;> omega

/-- Either the chunk's write did not extend the file within its range, or the bytes past the
chunk are none. -/
theorem pwBytes_chunk_end (sz off : Nat) (data : List w8) (j nn c k : Nat)
    (ys : List (w8 × Bool)) (hk : k ≤ c) (hc : nn + c ≤ data.length)
    (hyl : ys.length = min (off + data.length) (pwSize sz off j) - min off sz) :
    min (off + nn + c) (pwSize (pwSize sz off j) (off + nn) k) =
        min (off + nn + c) (pwSize sz off j) ∨
      ys.drop (min (off + nn + c) (pwSize sz off j) - min off sz) = [] := by
  generalize pwSize sz off j = s at hyl ⊢
  unfold pwSize
  by_cases hk0 : k = 0
  · left; simp [hk0]
  · simp only [hk0, ite_false]
    by_cases h : off + nn + k ≤ s
    · left; omega
    · right; apply List.drop_eq_nil_of_le; omega

set_option maxHeartbeats 2000000 in
/-- A write of the first `k` bytes of the chunk `cd = (data.drop nn).take c` at `off + nn` over
the file a write of the first `j ≥ nn` bytes of `data` at `off` left: the bytes before the chunk,
what the chunk's write left of its range, and the bytes after it, are the bytes a write of the
first `max j (nn + k)` bytes of `data` leaves. -/
theorem pwBytes_chunk (sz off : Nat) (data cd : List w8) (j nn c k : Nat)
    (xs ys : List (w8 × Bool))
    (hnj : nn ≤ j) (hj : j ≤ data.length) (hc : nn + c ≤ data.length) (hk : k ≤ c)
    (hcd : cd = (data.drop nn).take c)
    (hys : ys.map Prod.fst = (pwBytes sz off data j xs).map Prod.fst) :
    (ys.take (min (off + nn) (pwSize sz off j) - min off sz) ++
      pwBytes (pwSize sz off j) (off + nn) cd k
        ((ys.drop (min (off + nn) (pwSize sz off j) - min off sz)).take
          (min (off + nn + c) (pwSize sz off j) - min (off + nn) (pwSize sz off j))) ++
      ys.drop (min (off + nn + c) (pwSize sz off j) - min off sz)).map Prod.fst =
    (pwBytes sz off data (max j (nn + k)) xs).map Prod.fst := by
  have hyl : ys.length = min (off + data.length) (pwSize sz off j) - min off sz := by
    have := congrArg List.length hys; simp only [List.length_map, pwBytes_length] at this; exact this
  have hcdl : cd.length = c := by rw [hcd]; simp; omega
  have hcdv : ∀ i, i < c → cd.getD i 0 = data.getD (nn + i) 0 := by
    intro i hi
    rw [hcd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi, List.getElem?_drop]
  have hsz : sz ≤ pwSize sz off j := by unfold pwSize; split <;> omega
  have hsj : 0 < j → off + j ≤ pwSize sz off j := by unfold pwSize; split <;> omega
  have hval : ∀ i (hi : i < ys.length),
      ys[i].1 = pwByte off data j (min off sz) xs (min off sz + i) := by
    intro i hi
    have := congrArg (·[i]?) hys
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show i < (pwBytes sz off data j xs).length by
        rw [pwBytes_length]; omega), Option.map_some, Option.some.injEq] at this
    rw [this, pwBytes_getElem]
  -- byte `p` of the file of `j` is byte `p` of the file of `max j (nn + k)`, outside the chunk's
  -- written bytes
  have hout : ∀ p, (p < off + nn ∨ off + nn + k ≤ p) →
      pwByte off data j (min off sz) xs p = pwByte off data (max j (nn + k)) (min off sz) xs p := by
    intro p hp
    unfold pwByte
    by_cases c1 : p < off
    · rw [if_pos c1, if_pos c1]
    · rw [if_neg c1, if_neg c1]
      by_cases c3 : p < off + j
      · rw [if_pos c3, if_pos (by omega)]
      · rw [if_neg c3, if_neg (by omega)]
  generalize hs : pwSize sz off j = s at hyl hsz hsj hval ⊢
  have hs2 : pwSize s (off + nn) k = pwSize sz off (max j (nn + k)) := by
    rw [← hs]; exact pwSize_chunk sz off j nn k hnj
  generalize ha : min (off + nn) s - min off sz = a
  generalize hb : min (off + nn + c) s - min off sz = b
  have hmidl : ((ys.drop a).take (min (off + nn + c) s - min (off + nn) s)).length =
      min (off + nn + c) s - min (off + nn) s := by
    simp only [List.length_take, List.length_drop]; omega
  have hpl := pwBytes_length s (off + nn) cd k
    ((ys.drop a).take (min (off + nn + c) s - min (off + nn) s))
  rw [hcdl] at hpl
  have hend := pwBytes_chunk_end sz off data j nn c k ys hk hc (hs ▸ hyl)
  rw [hs, hb] at hend
  have hlenJ := pwBytes_length sz off data (max j (nn + k)) xs
  rw [← hs2] at hlenJ
  have hs2a : s ≤ pwSize s (off + nn) k := by unfold pwSize; split <;> omega
  have hs2b : pwSize s (off + nn) k = s ∨
      (0 < k ∧ pwSize s (off + nn) k = off + nn + k) := by unfold pwSize; split <;> omega
  clear hs2
  generalize pwSize s (off + nn) k = s2 at hpl hlenJ hend hs2a hs2b ⊢
  apply List.ext_getElem
  · simp only [List.length_map, List.length_append, List.length_take, List.length_drop, hpl,
      hlenJ, hyl]
    rcases hend with h | h
    · have h22 : s2 = s := by
        rcases hs2b with h3 | ⟨h3, h4⟩
        · exact h3
        · subst h4; omega
      subst h22; omega
    · have := congrArg List.length h
      simp only [List.length_drop, List.length_nil] at this
      rcases hs2b with h3 | ⟨h3, h4⟩
      · subst h3; omega
      · subst h4; omega
  · intro i h1 h2
    simp only [List.getElem_map]
    rw [pwBytes_getElem _ _ _ _ _ _ (by simpa using h2)]
    simp only [List.length_map, List.length_append, List.length_take, List.length_drop] at h1
    rw [List.getElem_append]
    split
    · rename_i hlt
      simp only [List.length_append, List.length_take] at hlt
      rw [List.getElem_append]
      split
      · rename_i hlt2
        simp only [List.length_take] at hlt2
        rw [List.getElem_take, hval i (by omega)]
        exact hout _ (.inl (by omega))
      · rename_i hlt2
        simp only [List.length_take, Nat.not_lt] at hlt2
        have hma : min a ys.length = a := by omega
        rw [hma] at hlt2 hlt
        simp only [List.length_take, hma]
        rw [pwBytes_getElem _ _ _ _ _ _ (by omega)]
        rw [show min (off + nn) s + (i - a) = min off sz + i by omega]
        unfold pwByte
        by_cases c1 : min off sz + i < off + nn
        · -- in the chunk's zero gap: past the file of `j`, so `j = 0`
          rw [if_pos c1]
          have hj0 : j = 0 := by
            apply Classical.byContradiction; intro h; have := hsj (by omega); omega
          rw [if_pos (by omega)]
        · rw [if_neg c1]
          by_cases c2 : min off sz + i < off + nn + k
          · rw [if_pos c2, if_neg (by omega), if_pos (by omega),
              show min off sz + i - (off + nn) = min off sz + i - off - nn by omega,
              hcdv _ (by omega), show nn + (min off sz + i - off - nn) = min off sz + i - off by omega]
          · rw [if_neg c2]
            have hpk : min off sz + i < s := by
              rw [hpl] at hlt; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_take,
              if_pos (by omega), List.getElem?_drop,
              List.getElem?_eq_getElem (show a + (min off sz + i - min (off + nn) s) < ys.length by
                omega)]
            simp only [Option.getD_some]
            rw [hval _ (by omega), show min off sz + (a + (min off sz + i - min (off + nn) s)) =
              min off sz + i by omega]
            rw [hout (min off sz + i) (.inr (by omega))]
            unfold pwByte
            rw [if_neg (show ¬ min off sz + i < off from by omega)]
    · rename_i hlt
      simp only [List.length_append, List.length_take, Nat.not_lt] at hlt
      have hma : min a ys.length = a := by omega
      rw [hma, hpl] at hlt
      have hbl : b ≤ ys.length := by omega
      have hsfx : a + (min (off + nn + c) s2 - min (off + nn) s) = b := by
        rcases hend with h | h
        · rw [h]; omega
        · have := congrArg List.length h
          simp only [List.length_drop, List.length_nil] at this
          omega
      simp only [List.length_append, List.length_take, hma, hpl]
      rw [List.getElem_drop]
      rw [hval _ (by omega)]
      rw [show b + (i - (a + (min (off + nn + c) s2 - min (off + nn) s))) = i
        by omega]
      exact hout _ (.inr (by omega))

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem osBytes_take_drop (p : GoString) (lo : Nat) (dq : DFrac) (ys : List (w8 × Bool)) (a : Nat)
    (ha : a ≤ ys.length) :
    osBytes (L := L) p lo dq ys ⊣⊢ osBytes p lo dq (ys.take a) ∗ osBytes p (lo + a) dq (ys.drop a) := by
  conv => lhs; rw [← List.take_append_drop a ys]
  unfold osBytes
  refine (bytesG_append _ _ _ _ _ _).trans ?_
  rw [List.length_take, Nat.min_eq_left ha]
  exact .rfl

/-- The bytes `ys` from `lo` on, cut at `a ≤ b`: the chunk's `[a, b)` (`n = b - a` bytes) from
`lo' = lo + a`, the rest from `lo'' = lo + b`. -/
theorem osBytes_split3_range (p : GoString) (lo lo' lo'' : Nat) (dq : DFrac) (ys : List (w8 × Bool))
    (a b n : Nat) (hab : a ≤ b) (hb : b ≤ ys.length) (hn : n = b - a) (h1 : lo' = lo + a)
    (h2 : lo'' = lo + b) :
    osBytes (L := L) p lo dq ys ⊢ osBytes p lo dq (ys.take a) ∗
      osBytes p lo' dq ((ys.drop a).take n) ∗ osBytes p lo'' dq (ys.drop b) := by
  subst hn
  refine (osBytes_take_drop p lo dq ys a (by omega)).1.trans (sep_mono .rfl ?_)
  refine (osBytes_take_drop p (lo + a) dq (ys.drop a) (b - a) (by simp; omega)).1.trans ?_
  rw [List.drop_drop, show a + (b - a) = b by omega, show lo + a + (b - a) = lo + b by omega, ← h1, ← h2]

/-- Three runs of bytes, the third beginning where the second ends unless it is empty. -/
theorem osBytes_app3 (p : GoString) (lo a2 a3 : Nat) (dq : DFrac) (L1 L2 L3 : List (w8 × Bool))
    (h2 : a2 = lo + L1.length) (h3 : a3 = a2 + L2.length ∨ L3 = []) :
    osBytes (L := L) p lo dq L1 ∗ osBytes p a2 dq L2 ∗ osBytes p a3 dq L3 ⊢
      osBytes p lo dq (L1 ++ L2 ++ L3) := by
  unfold osBytes
  refine BIBase.Entails.trans ?_ (bytesG_append _ _ _ _ _ _).2
  refine BIBase.Entails.trans ?_ (sep_mono (bytesG_append _ _ _ _ _ _).2 .rfl)
  rcases h3 with h3 | h3
  · subst h2 h3
    rw [List.length_append, Nat.add_assoc]
    iintro ⟨H1, H2, H3⟩; iframe
  · subst h2 h3
    iintro ⟨H1, H2, -⟩; iframe; iapply (bytesG_nil _ _ _ _).2; iempintro

end res

end Perennial
