/-
A `pwrite` in chunks (`os.File.WriteAt`'s model, `TrustedCode/os.lean`, writes at most 1 GiB per
`pwrite`), over the per-byte extension (`GooseLang/Ext/Fs/Write.lean`): an attempt of the first `k`
bytes of the chunk `cd = (data.drop nn).take c` at `off + nn`, over the file a write of the first
`j ≥ nn` bytes of `data` at `off` left, leaves the file a write of the first `max j (nn + k)` bytes
leaves (`pwSize_chunk`; the values, `pwValsG_chunk`; the `OsMeta`, `pwPost_chunk`, whose announced
range is the furthest chunk's). The attempt takes the middle of the range's bytes
(`osBytes_split3_range`) and gives back bytes that end where the rest begins, or the rest is empty
(`osBytes_app3`). The write may start past the end of the file (`pwValsG`: bytes from
`min off size`, the zero gap).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

theorem pwSize_chunk (sz off j nn k : Nat) (hnj : nn ≤ j) :
    pwSize (pwSize sz off j) (off + nn) k = pwSize sz off (max j (nn + k)) := by
  unfold pwSize
  by_cases hj : j = 0 <;> by_cases hk : k = 0 <;> simp [hj, hk] <;> omega

/-- Byte `p` of a write of the first `j` bytes is that of a write of the first `max j (nn + k)`,
outside the bytes `[off + nn, off + nn + k)` the attempt landed. -/
theorem pwByteG_out (lo off : Nat) (data : List w8) (j nn k : Nat) (xs : List ByteG) (p : Nat)
    (hnj : nn ≤ j) (hp : p < off + nn ∨ off + nn + k ≤ p) :
    pwByteG lo off data j xs p = pwByteG lo off data (max j (nn + k)) xs p := by
  unfold pwByteG
  by_cases h1 : off ≤ p ∧ p < off + j
  · rw [if_pos h1, if_pos ⟨h1.1, by omega⟩]
  · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, by omega⟩)]

theorem pwValsG_zero (sz off : Nat) (data : List w8) (xs : List ByteG)
    (hxl : xs.length = min (off + data.length) sz - min off sz) :
    pwValsG sz off data 0 xs = xs.map Prod.fst := by
  apply List.ext_getElem
  · simp [pwValsG_length, pwSize, hxl]
  · intro i h1 h2
    simp only [pwValsG, List.getElem_map, List.getElem_range, pwByteG]
    rw [if_neg (by omega), List.getD_eq_getElem?_getD, show min off sz + i - min off sz = i by omega,
      List.getElem?_eq_getElem (by simpa using h2)]
    simp

set_option maxHeartbeats 1000000 in
/-- The values after a chunk's attempt: the bytes before the attempt's, what it left of its
range (`L2`, of the values `pwValsG` gives), and the bytes after it, are the values of a write of
the first `max j (nn + k)` bytes of `data`. -/
theorem pwValsG_chunk (sz off : Nat) (data cd : List w8) (j nn c k : Nat)
    (xs ys : List ByteG) (L2 : List ByteG)
    (hnj : nn ≤ j) (hj : j ≤ data.length) (hc : nn + c ≤ data.length) (hk : k ≤ c)
    (hcd : cd = (data.drop nn).take c)
    (hxl : xs.length = min (off + data.length) sz - min off sz)
    (hys : ys.map Prod.fst = pwValsG sz off data j xs)
    (hL2 : L2.map Prod.fst = pwValsG (pwSize sz off j) (off + nn) cd k
      ((ys.drop (min (off + nn) (pwSize sz off j) - min off sz)).take
        (min (off + nn + c) (pwSize sz off j) - min (off + nn) (pwSize sz off j)))) :
    (ys.take (min (off + nn) (pwSize sz off j) - min off sz) ++ L2 ++
      ys.drop (min (off + nn + c) (pwSize sz off j) - min off sz)).map Prod.fst =
    pwValsG sz off data (max j (nn + k)) xs := by
  have hyl : ys.length = min (off + data.length) (pwSize sz off j) - min off sz := by
    have := congrArg List.length hys; simp only [List.length_map, pwValsG_length] at this
    exact this
  have hcdl : cd.length = c := by rw [hcd]; simp; omega
  have hcdv : ∀ i, i < c → cd.getD i 0 = data.getD (nn + i) 0 := by
    intro i hi
    rw [hcd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi, List.getElem?_drop]
  have hval : ∀ i (hi : i < ys.length),
      ys[i].1 = pwByteG (min off sz) off data j xs (min off sz + i) := by
    intro i hi
    have := congrArg (·[i]?) hys
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show i < (pwValsG sz off data j xs).length by
        rw [pwValsG_length]; omega), Option.map_some, Option.some.injEq] at this
    rw [this]; simp [pwValsG]
  have hsz : sz ≤ pwSize sz off j := by unfold pwSize; split <;> omega
  have hsj : 0 < j → off + j ≤ pwSize sz off j := by unfold pwSize; split <;> omega
  have hsj0 : j = 0 → pwSize sz off j = sz := by intro h; simp [pwSize, h]
  have hs2 : pwSize (pwSize sz off j) (off + nn) k = pwSize sz off (max j (nn + k)) :=
    pwSize_chunk sz off j nn k hnj
  have hxl2 : xs.length ≤ sz - min off sz := by omega
  generalize hs : pwSize sz off j = s at hyl hsz hsj hsj0 hs2 hL2 ⊢
  generalize hlo : min off sz = lo at hyl hxl hxl2 hval hL2 ⊢
  have hlo1 : lo ≤ off := by omega
  have hlo2 : lo ≤ sz := by omega
  have hlo3 : lo = off ∨ (lo = sz ∧ sz < off) := by omega
  generalize hlo' : min (off + nn) s = lo' at hL2 ⊢
  generalize he : min (off + nn + c) s = e at hL2 ⊢
  have hlo'1 : lo ≤ lo' := by omega
  have hlo'2 : lo' ≤ e := by omega
  have he1 : e ≤ min (off + data.length) s := by omega
  generalize hmid : (ys.drop (lo' - lo)).take (e - lo') = mid at hL2
  have hmidl : mid.length = e - lo' := by
    rw [← hmid]; simp only [List.length_take, List.length_drop]; omega
  have hmidv : ∀ q (hq : q < mid.length), mid[q] = ys[lo' - lo + q]'(by omega) := by
    intro q hq; subst hmid; simp
  have hL2l : L2.length = min (off + nn + cd.length) (pwSize s (off + nn) k) - min (off + nn) s := by
    have := congrArg List.length hL2; simp only [List.length_map, pwValsG_length] at this
    exact this
  rw [hcdl, hlo'] at hL2l
  have hL2v : ∀ q (hq : q < L2.length),
      L2[q].1 = pwByteG lo' (off + nn) cd k mid (lo' + q) := by
    intro q hq
    have := congrArg (·[q]?) hL2
    simp only [List.getElem?_map, List.getElem?_eq_getElem hq,
      List.getElem?_eq_getElem (show q < (pwValsG s (off + nn) cd k mid).length by
        rw [pwValsG_length]; rw [hcdl, hlo']; omega), Option.map_some, Option.some.injEq] at this
    rw [this]; simp [pwValsG, hlo']
  have hlenJ := pwValsG_length sz off data (max j (nn + k)) xs
  rw [← hs2, hlo] at hlenJ
  have hs2a : s ≤ pwSize s (off + nn) k := by unfold pwSize; split <;> omega
  have hs2b : pwSize s (off + nn) k = s ∨
      (0 < k ∧ s < off + nn + k ∧ pwSize s (off + nn) k = off + nn + k) := by
    unfold pwSize; split <;> omega
  have hend : pwSize s (off + nn) k = s ∨ e - lo = ys.length := by
    rcases hs2b with h | ⟨h1, h2, h3⟩
    · left; exact h
    · right; omega
  have hout := fun p hp => pwByteG_out lo off data j nn k xs p hnj hp
  clear hs2 hL2 hys
  generalize hS2 : pwSize s (off + nn) k = s2 at hL2l hlenJ hs2a hs2b hend
  apply List.ext_getElem
  · simp only [List.length_map, List.length_append, List.length_take, List.length_drop, hL2l,
      hlenJ, hyl]
    rcases hs2b with h | ⟨h1, h2, h3⟩
    · subst h; omega
    · omega
  · intro i h1 h2
    simp only [List.getElem_map]
    simp only [List.length_map, List.length_append, List.length_take, List.length_drop] at h1
    have hJ : (pwValsG sz off data (max j (nn + k)) xs)[i] =
        pwByteG (min off sz) off data (max j (nn + k)) xs (min off sz + i) := by
      simp [pwValsG]
    rw [hJ, hlo]
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
        have hma : min (lo' - lo) ys.length = lo' - lo := by omega
        rw [hma] at hlt2 hlt
        simp only [List.length_take, hma]
        rw [hL2v _ (by omega), show lo' + (i - (lo' - lo)) = lo + i by omega]
        unfold pwByteG
        by_cases c2 : off + nn ≤ lo + i ∧ lo + i < off + nn + k
        · rw [if_pos c2, if_pos ⟨by omega, by omega⟩,
            show lo + i - (off + nn) = lo + i - off - nn by omega, hcdv _ (by omega),
            show nn + (lo + i - off - nn) = lo + i - off by omega]
        · rw [if_neg c2]
          by_cases hq : lo + i - lo' < mid.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
            simp only [Option.getD_some]
            rw [hmidv _ hq, hval _ (by omega), show lo + (lo' - lo + (lo + i - lo')) = lo + i by omega]
            have := hout (lo + i) (by omega)
            unfold pwByteG at this
            exact this
          · -- past the old size, in the attempt's zero gap: the write started past the end
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            have hgap : s ≤ lo + i := by omega
            have hj0 : j = 0 := by
              apply Classical.byContradiction; intro h; have := hsj (by omega); omega
            have hss := hsj0 hj0
            rw [if_neg (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    · rename_i hlt
      simp only [List.length_append, List.length_take, Nat.not_lt] at hlt
      have hma : min (lo' - lo) ys.length = lo' - lo := by omega
      rw [hma, hL2l] at hlt
      have hsfx : lo' - lo + (min (off + nn + c) s2 - lo') = e - lo := by
        rcases hend with h | h
        · subst h; omega
        · omega
      simp only [List.length_append, List.length_take, hma, hL2l]
      rw [List.getElem_drop, hval _ (by omega),
        show e - lo + (i - (lo' - lo + (min (off + nn + c) s2 - lo'))) = i by omega]
      apply hout
      rcases hs2b with h | ⟨h1, h2, h3⟩
      · subst h
        right
        by_cases hk0 : k = 0
        · omega
        · have : off + nn + k ≤ s2 := by
            have h5 := hS2; unfold pwSize at h5; rw [if_neg hk0] at h5; omega
          omega
      · right; omega

/-- Either the chunk's attempt did not extend the file within its range, or the bytes past the
chunk are none. -/
theorem pwChunk_end {α : Type} (s off len nn c k lo : Nat) (ys : List α) (hk : k ≤ c)
    (hc : nn + c ≤ len) (hyl : ys.length = min (off + len) s - lo) :
    min (off + nn + c) (pwSize s (off + nn) k) = min (off + nn + c) s ∨
      ys.drop (min (off + nn + c) s - lo) = [] := by
  unfold pwSize
  by_cases hk0 : k = 0
  · left; simp [hk0]
  · simp only [hk0, ite_false]
    by_cases h : off + nn + k ≤ s
    · left; omega
    · right; apply List.drop_eq_nil_of_le; omega

/-- A write of `cs` bytes at `off + nn` (the chunk) over the `OsMeta` a write of `j` bytes at
`off` left, whose first steps announced `[min off size, off + a)`, leaves the `OsMeta` of a write of
`max j (nn + k)` bytes whose first steps announced `[min off size, off + nn + cs)`. -/
theorem pwPost_chunk (m : OsMeta) (off a nn j cs k : Nat) (hml : m.lo ≤ m.size) (hnn : nn ≤ j)
    (hja : j ≤ a) (ha : a ≤ nn + cs) (ha0 : 0 < a) (hk : k ≤ cs) (hcs0 : 0 < cs) :
    pwPost (pwPost m off a j) (off + nn) cs k = pwPost m off (nn + cs) (max j (nn + k)) := by
  have hS1 : m.size ≤ pwSize m.size off j := by unfold pwSize; split <;> omega
  have hS2 : 0 < j → off + j ≤ pwSize m.size off j := by unfold pwSize; split <;> omega
  have hS3 : j = 0 → pwSize m.size off j = m.size := by intro h; simp [pwSize, h]
  have hlo' : min off m.size ≤ min (off + nn) (pwSize m.size off j) := by omega
  have hlo'' : min (off + nn) (pwSize m.size off j) ≤ off + a := by omega
  have hsz : pwSize (pwSize m.size off j) (off + nn) k = pwSize m.size off (max j (nn + k)) :=
    pwSize_chunk _ _ _ _ _ hnn
  apply os.osMeta_eq
  · exact hsz
  · simp only [pwPost, announce_lo]; unfold pwSize; split <;> omega
  · simp only [pwPost, announce_hi]; unfold pwSize; split <;> omega
  · simp only [pwPost, announce_maps]
  · simp only [pwPost, announce_dlo, announce_dhi, os.touch_dlo, os.touch_dhi]
    by_cases h3 : m.dhi ≤ m.dlo <;>
      simp only [h3, if_true, if_false, show ¬ off + a ≤ min off m.size by omega,
        show ¬ off + nn + cs ≤ min (off + nn) (pwSize m.size off j) by omega,
        show ¬ off + (nn + cs) ≤ min off m.size by omega] <;> (repeat' split) <;> omega
  · simp only [pwPost, announce_dlo, announce_dhi, os.touch_dlo, os.touch_dhi]
    by_cases h3 : m.dhi ≤ m.dlo <;>
      simp only [h3, if_true, if_false, show ¬ off + a ≤ min off m.size by omega,
        show ¬ off + nn + cs ≤ min (off + nn) (pwSize m.size off j) by omega,
        show ¬ off + (nn + cs) ≤ min off m.size by omega] <;> (repeat' split) <;> omega
  · simp only [pwPost, announce_zf, Option.map_map]
    cases m.zf with
    | none => rfl
    | some z =>
      simp only [Option.map_some, Function.comp, Option.some.injEq,
        show min off m.size < off + a by omega,
        show min (off + nn) (pwSize m.size off j) < off + nn + cs by omega,
        show min off m.size < off + (nn + cs) by omega, if_true]
      omega
  · apply GMap.ext; intro b
    simp only [pwPost, announce_tc, announce_size, inRange, Bool.and_eq_true, decide_eq_true_eq]
    (repeat' split) <;> first | rfl | omega
  · simp [pwPost]

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem osBytes_take_drop (p : Ino) (lo : Nat) (dq : DFrac) (ys : List ByteG) (a : Nat)
    (ha : a ≤ ys.length) :
    osBytes (L := L) p lo dq ys ⊣⊢ osBytes p lo dq (ys.take a) ∗ osBytes p (lo + a) dq (ys.drop a) := by
  conv => lhs; rw [← List.take_append_drop a ys]
  unfold osBytes
  refine (bytesG_append _ _ _ _ _ _).trans ?_
  rw [List.length_take, Nat.min_eq_left ha]
  exact .rfl

/-- The bytes `ys` from `lo` on, cut at `a ≤ b`: the chunk's `[a, b)` (`n = b - a` bytes) from
`lo' = lo + a`, the rest from `lo'' = lo + b`. -/
theorem osBytes_split3_range (p : Ino) (lo lo' lo'' : Nat) (dq : DFrac) (ys : List ByteG)
    (a b n : Nat) (hab : a ≤ b) (hb : b ≤ ys.length) (hn : n = b - a) (h1 : lo' = lo + a)
    (h2 : lo'' = lo + b) :
    osBytes (L := L) p lo dq ys ⊢ osBytes p lo dq (ys.take a) ∗
      osBytes p lo' dq ((ys.drop a).take n) ∗ osBytes p lo'' dq (ys.drop b) := by
  subst hn
  refine (osBytes_take_drop p lo dq ys a (by omega)).1.trans (sep_mono .rfl ?_)
  refine (osBytes_take_drop p (lo + a) dq (ys.drop a) (b - a) (by simp; omega)).1.trans ?_
  rw [List.drop_drop, show a + (b - a) = b by omega, show lo + a + (b - a) = lo + b by omega, ← h1, ← h2]

/-- Three runs of bytes, the third beginning where the second ends unless it is empty. -/
theorem osBytes_app3 (p : Ino) (lo a2 a3 : Nat) (dq : DFrac) (L1 L2 L3 : List ByteG)
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

section fin
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `wp_osPWriteFinishKG` forgetting the candidates past the size (`wp_osPWriteFinish`, anywhere). -/
theorem wp_osPWriteFinishG (t : Nat) (p : Ino) (off : Nat) (data : List w8) (m : OsMeta)
    (xs : List ByteG) (n : Nat) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ pwTokG (L := L) t p off data m xs n -∗
      (∀ k : Nat, ∀ e : w64, ∀ zs : List Cands,
        ⌜k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧
          zs.length = pwSize m.size off k - m.size ∧
          ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ -∗
        ⌜PwCut off data.length k⌝ -∗
        osMeta (L := L) p (DFrac.own 1) (pwPost m off data.length k) -∗
        osBytes (L := L) p (min off m.size) (DFrac.own 1) (pwBytesG m.size off data k n xs zs) -∗
        mcells m.maps (min off m.size) (off + data.length) (pwCellG m.size off data k xs) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  iintro #Hinv Ht HΦ
  iapply wp_osPWriteFinishKG false t p off data m xs n hE Φ $$ Hinv Ht
  iintro %k %e %zs %h %- %hpc Hm Hbs Hc
  rw [pwPostKG_false]
  iapply HΦ $$ %k %e %zs %h %hpc Hm Hbs Hc

end fin

end Fs
end Perennial
