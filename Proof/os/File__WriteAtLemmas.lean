/-
The lemmas of `File__WriteAt.lean`'s proof (the attempts' arithmetic, `pwPost_step`, `pwOut_step`,
`pwCut_step`), in a module of their own so that `WriteLongStep.lean` imports them without the
proof (import tiers, 2026-11-18).
-/
module

public import Proof.os.ErrorOk
public import Spec.os.File__WriteAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem pwSize_ge (sz off k : Nat) : sz ≤ pwSize sz off k := by
  unfold pwSize; split <;> omega

theorem pwSize_from (sz off j nn k : Nat) (hnn : nn ≤ j) :
    pwSize (pwSize sz off j) (off + nn) k = pwSize sz off (max j (nn + k)) := by
  unfold pwSize
  by_cases hj : j = 0
  · have : nn = 0 := by omega
    subst hj this; simp
  · by_cases hk : k = 0
    · subst hk; simp [hj, Nat.max_eq_left hnn]
    · rw [if_neg hk, if_neg hj, if_neg (by omega)]; omega

theorem pwSize_le (sz off k n : Nat) (hk : k ≤ n) : pwSize sz off k ≤ max sz (off + n) := by
  unfold pwSize; split <;> omega

theorem pwSize_off (sz off j nn : Nat) (hoff : off ≤ sz) (hnn : nn ≤ j) :
    off + nn ≤ pwSize sz off j := by
  unfold pwSize; split
  · have : nn = 0 := by omega
    omega
  · omega

@[simp] theorem pwPost_size (m : OsMeta) (off n k : Nat) :
    (pwPost m off n k).size = pwSize m.size off k := rfl

/-- A write's next attempt, from where a short one stopped, announces nothing new: the `OsMeta`
it leaves is the first attempt's, with the size the two leave. -/
theorem pwPost_step (m : OsMeta) (off n nn j k : Nat) (hoff : off ≤ m.size) (hnn : nn ≤ j)
    (hj : j ≤ n) (hnl : nn < n) (hk : k ≤ n - nn) :
    pwPost (pwPost m off n j) (off + nn) (n - nn) k = pwPost m off n (max j (nn + k)) := by
  have hS := pwSize_off m.size off j nn hoff hnn
  have hS2 := pwSize_le m.size off j n hj
  have hS3 := pwSize_ge m.size off j
  have hm1 : min off m.size = off := Nat.min_eq_left hoff
  apply os.osMeta_eq
  · exact pwSize_from _ _ _ _ _ hnn
  · simp only [pwPost, announce_lo]; omega
  · simp only [pwPost, announce_hi]; omega
  · simp only [pwPost, announce_maps]
  · simp only [pwPost, announce_dlo, announce_dhi, os.touch_dlo, os.touch_dhi, hm1]
    by_cases h3 : m.dhi ≤ m.dlo <;>
      simp only [h3, if_true, if_false, show ¬ off + n ≤ off by omega] <;> (repeat' split) <;> omega
  · simp only [pwPost, announce_dlo, announce_dhi, os.touch_dlo, os.touch_dhi, hm1]
    by_cases h3 : m.dhi ≤ m.dlo <;>
      simp only [h3, if_true, if_false, show ¬ off + n ≤ off by omega] <;> (repeat' split) <;> omega
  · simp only [pwPost, announce_zf, Option.map_map, hm1]
    cases m.zf with
    | none => rfl
    | some z =>
      simp only [Option.map_some, Function.comp, Option.some.injEq,
        show off < off + n by omega, if_true, show off + nn + (n - nn) = off + n by omega]
      (repeat' split) <;> omega
  · apply GMap.ext; intro b
    simp only [pwPost, announce_tc, announce_size, hm1, inRange, Bool.and_eq_true, decide_eq_true_eq]
    (repeat' split) <;> first | rfl | omega
  · simp [pwPost]
  · -- the page cache known zero: raised once the data is all written (`pwCz`)
    show pwCz (pwPost m off n j) (off + nn) (n - nn) k = pwCz m off n (max j (nn + k))
    have hz1 : (pwPost m off n j).zf = m.zf.map (fun z => max z (off + n)) := by
      simp only [pwPost, announce_zf, hm1]
      cases m.zf with
      | none => rfl
      | some z => simp only [Option.map_some, show off < off + n by omega, if_true]
    have hcz1 : (pwPost m off n j).cz = pwCz m off n j := rfl
    unfold pwCz
    rw [hz1, hcz1]
    unfold pwCz
    cases m.zf with
    | none => rfl
    | some z =>
      simp only [Option.map_some, show off + nn + (n - nn) = off + n by omega]
      (repeat' split) <;> omega
  · simp [pwPost]

/-- The bytes after a write's next attempt, from `nn ≤ j` (where a short attempt stopped), over
the bytes as the first `j` bytes left them: as the first `max j (nn + k)` bytes leave them. -/
theorem pwOut_step (m : OsMeta) (off nn : Nat) (data : List w8) (j k nst : Nat)
    (xs ys : List ByteG) (zs : List Cands)
    (hoff : off ≤ m.size) (hnn : nn ≤ j) (hj : j ≤ data.length) (hk : k ≤ data.length - nn)
    (hlen : xs.length = min (off + data.length) m.size - off)
    (hinv : (j = 0 ∧ nn = 0 ∧ ys = xs) ∨ os.PwOut m off data j xs ys) :
    os.PwOut m off data (max j (nn + k)) xs
      (ys.take nn ++ pwBytes (pwSize m.size off j) (off + nn) (data.drop nn) k nst (ys.drop nn) zs) := by
  have hyl : ys.length = min (off + data.length) (pwSize m.size off j) - off := by
    rcases hinv with ⟨rfl, -, rfl⟩ | h
    · simp [pwSize, hlen]
    · exact h.1
  have hval : ∀ i (hi : i < ys.length), ys[i].1 = pwByte off data j xs (off + i) := by
    rcases hinv with ⟨rfl, -, rfl⟩ | h
    · intro i hi
      simp only [pwByte, Nat.add_zero, show ¬ off + i < off by omega, if_false,
        show off + i - off = i by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some]
    · exact fun i hi => (h.2 i hi).1
  have hcand : ∀ i (hi : i < ys.length), ∃ c0 extra, ys[i].2 = c0 ++ extra ∧
      (∀ q ∈ extra, q.1 = data.getD i 0) ∧ ∀ (h : i < xs.length), c0 = xs[i].2 := by
    rcases hinv with ⟨rfl, -, rfl⟩ | h
    · intro i hi
      exact ⟨ys[i].2, [], by simp, fun q hq => (by simp at hq), fun _ => rfl⟩
    · intro i hi
      obtain ⟨c0, extra, h1, -, h3, h4⟩ := (h.2 i hi).2
      exact ⟨c0, extra, h1, h3, h4⟩
  have hxy : xs.length ≤ ys.length := by
    rw [hyl, hlen]; have := pwSize_ge m.size off j; omega
  have hS := pwSize_off m.size off j nn hoff hnn
  have hnny : nn ≤ ys.length := by rw [hyl]; omega
  have hjy : j ≤ ys.length := by
    rw [hyl]; unfold pwSize; split <;> omega
  have hminS : min (off + nn) (pwSize m.size off j) = off + nn := Nat.min_eq_left hS
  have hend : off + nn + (data.drop nn).length = off + data.length := by
    rw [List.length_drop]; omega
  have hpw := pwSize_from m.size off j nn k hnn
  have hlenT : (ys.take nn ++ pwBytes (pwSize m.size off j) (off + nn) (data.drop nn) k nst
      (ys.drop nn) zs).length = min (off + data.length) (pwSize m.size off (max j (nn + k))) - off := by
    simp only [List.length_append, List.length_take, Nat.min_eq_left hnny, pwBytes_length, hend, hpw]
    have : off + nn ≤ pwSize m.size off (max j (nn + k)) := by
      rw [← hpw]; exact Nat.le_trans hS (pwSize_ge _ _ _)
    omega
  refine ⟨hlenT, fun i hi => ?_⟩
  rw [List.getElem_append]
  split
  · rename_i hlt
    simp only [List.length_take, Nat.min_eq_left hnny] at hlt
    rw [List.getElem_take]
    refine ⟨?_, ?_⟩
    · rw [hval i (by omega)]
      unfold pwByte
      rw [if_pos (show off + i < off + j by omega), if_pos (show off + i < off + max j (nn + k) by omega)]
    · rcases hinv with ⟨-, rfl, -⟩ | h
      · omega
      · exact (h.2 i (by omega)).2
  · rename_i hlt
    simp only [List.length_take, Nat.min_eq_left hnny, Nat.not_lt] at hlt
    have hi2 : i - nn < (pwBytes (pwSize m.size off j) (off + nn) (data.drop nn) k nst (ys.drop nn) zs).length := by
      simp only [pwBytes_length, hend, hpw]
      have : off + nn ≤ pwSize m.size off (max j (nn + k)) := by
        rw [← hpw]; exact Nat.le_trans hS (pwSize_ge _ _ _)
      rw [hlenT] at hi
      omega
    try simp only [List.length_take, Nat.min_eq_left hnny]
    have hdi : (data.drop nn).getD (i - nn) 0 = data.getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
        show nn + (i - nn) = i by omega]
    refine ⟨?_, ?_⟩
    · rw [pwBytes_getElem _ _ _ _ _ _ _ _ hi2, show off + nn + (i - nn) = off + i by omega]
      unfold pwByte
      by_cases c2 : off + i < off + nn + k
      · rw [if_pos c2, if_pos (show off + i < off + max j (nn + k) by omega),
          show off + i - (off + nn) = i - nn by omega, hdi, show off + i - off = i by omega]
      · rw [if_neg c2, show off + i - (off + nn) = i - nn by omega, List.getD_eq_getElem?_getD,
          List.getElem?_drop, show nn + (i - nn) = i by omega]
        by_cases hiy : i < ys.length
        · rw [List.getElem?_eq_getElem hiy, Option.getD_some, hval i hiy]
          unfold pwByte
          by_cases c3 : off + i < off + j
          · rw [if_pos c3, if_pos (show off + i < off + max j (nn + k) by omega)]
          · rw [if_neg c3, if_neg (show ¬ off + i < off + max j (nn + k) by omega)]
        · rw [List.getElem?_eq_none (by omega), Option.getD_none]
          rw [if_neg (show ¬ off + i < off + max j (nn + k) by omega), show off + i - off = i by omega,
            List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    · simp only [pwBytes, List.getElem_map, List.getElem_range, List.length_drop]
      rw [show (data.drop nn).getD (i - nn) 0 = data.getD i 0 from hdi]
      by_cases hiy : i < ys.length
      · rw [if_pos (show i - nn < ys.length - nn by omega), List.getD_eq_getElem?_getD,
          List.getElem?_drop, show nn + (i - nn) = i by omega, List.getElem?_eq_getElem hiy,
          Option.getD_some]
        obtain ⟨c0, extra, h1, h3, h4⟩ := hcand i hiy
        refine ⟨c0, extra ++ [(data.getD i 0, nst)], by rw [h1, List.append_assoc], by simp, ?_, h4⟩
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact h3 q hq
        · rw [List.mem_singleton] at hq; subst hq; rfl
      · rw [if_neg (show ¬ i - nn < ys.length - nn by omega)]
        refine ⟨_, [(data.getD i 0, nst)], rfl, by simp, fun q hq => by
          rw [List.mem_singleton] at hq; subst hq; rfl, fun h => absurd h (by omega)⟩

/-- The bytes a write has landed after one more attempt are a page cut, from those before and the
attempt's. -/
theorem pwCut_step (off len nn j k : Nat) (hj : PwCut off len j) (hnj : nn ≤ j)
    (hnn : nn = 0 ∨ (off + nn) % osPageSize = 0) (hk : k ≤ len - nn) (hnl : nn < len)
    (hpc : PwCut (off + nn) (len - nn) k) : PwCut off len (max j (nn + k)) := by
  unfold PwCut at *
  unfold osPageSize at *
  obtain ⟨hj, hjm⟩ := hj
  obtain ⟨hpc, hpm⟩ := hpc
  rcases Nat.le_total j (nn + k) with h | h
  · rw [Nat.max_eq_right h]
    refine ⟨?_, by omega⟩
    rcases hpc with h0 | h0 | h0
    · subst h0; rcases hnn with h1 | h1
      · left; omega
      · right; right; simpa using h1
    · right; left; omega
    · right; right; rw [← Nat.add_assoc]; exact h0
  · rw [Nat.max_eq_left h]; exact ⟨hj, hjm⟩

/-- After a short attempt that succeeded, the next starts on a page boundary. -/
theorem pwCut_short (off len nn k : Nat) (hk0 : 0 < k) (hfull : nn + k ≠ len)
    (hpc : PwCut (off + nn) (len - nn) k) (hk : k ≤ len - nn) :
    nn + k = 0 ∨ (off + (nn + k)) % osPageSize = 0 := by
  unfold PwCut at hpc
  rcases hpc.1 with h0 | h0 | h0
  · omega
  · omega
  · right; rw [← Nat.add_assoc]; exact h0


end proof

end EtcdGrove
end Perennial
