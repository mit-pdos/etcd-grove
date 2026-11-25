/-
The pure steps of `Proof/os/WriteLong.lean`'s Löb induction (a `WriteAt` past 1 GiB, in chunks of
at most `maxRW`): one attempt from `nn` announcing the chunk `[off + nn, off + A')` over the file as a
write that announced its first `A ≤ A'` bytes and wrote its first `j` left it. `pwPostE_step`
generalizes `pwPost_step` (the crash low bound composes since `m.lo ≤ m.size`; the page cache known
zero is the last whole chunk's, `pwPostE`), `pwOutA_step` generalizes `pwOut_step` (the bytes split
in three around the chunk), `pwCutE_step` `pwCut_step`. Lean-first.
-/
module

public import Proof.os.File__WriteAt
public import Spec.os.WriteLong

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Fs

theorem wl_add30 (nnv : w64) (h : sint.Z nnv + 1073741824 < 2 ^ 63) (h0 : 0 ≤ sint.Z nnv) :
    sint.Z (nnv + W64 1073741824) = sint.Z nnv + 1073741824 := by
  word

theorem wl_W64_toNat (k : Nat) (h : k < 2 ^ 63) : (W64 k).toNat = k := by
  simp only [W64]; rw [BitVec.toNat_ofInt]; omega

theorem wl_len_eq (sl : GoSlice) (n : Nat) (h : sint.Z sl.len = n) (hn : n < 2 ^ 63) :
    sl.len = W64 n := by
  apply BitVec.eq_of_toInt_eq
  simp only [sint.Z] at h
  rw [h, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega

theorem wl_toNat_of_sintZ (mx : w64) (A' : Nat) (h : sint.Z mx = A') : mx.toNat = A' := by
  simp only [sint.Z] at h
  have h2 := BitVec.toInt_eq_toNat_cond mx
  split at h2 <;> omega

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem pwPostE_size (m : OsMeta) (off A j E : Nat) :
    (os.pwPostE m off A j E).size = pwSize m.size off j := rfl

theorem pwPostE_maps (m : OsMeta) (off A j E : Nat) :
    (os.pwPostE m off A j E).maps = m.maps := by
  simp [os.pwPostE, pwPost]

/-- On success, and up to `maxRW`, `pwPostE` is `pwPost`. -/
theorem pwPostE_self (m : OsMeta) (off A : Nat) : os.pwPostE m off A A A = pwPost m off A A := rfl

theorem pwPostE_one (m : OsMeta) (off A j : Nat) (hj : j ≤ A) :
    os.pwPostE m off A j (if j = A then A else 0) = pwPost m off A j := by
  by_cases h : j = A
  · subst h; simp only [if_true]; rfl
  · have : pwCz m off 0 0 = pwCz m off A j := by
      unfold pwCz; cases m.zf with
      | none => rfl
      | some z => simp only [Nat.lt_irrefl, false_and, if_false]; rw [if_neg (by omega)]
    simp only [h, if_false, os.pwPostE, this]
    rfl

/-- The first attempt, from `0`, as a `pwPostE`. -/
theorem pwPostE_base (m : OsMeta) (off A' k : Nat) (hk : k ≤ A') :
    pwPost m off A' k = os.pwPostE m off A' k (if k = A' then A' else 0) :=
  (pwPostE_one m off A' k hk).symm

theorem pwCz_le_raise (m : OsMeta) (off E A' : Nat) (hE : E ≤ A') (z : Nat) (hz : m.zf = some z)
    (hzA : z ≤ off + A') : pwCz m off E E ≤ max m.cz (pageEnd (off + A')) := by
  unfold pwCz; rw [hz]; dsimp only
  split
  · have := pageEnd_mono (show off + E ≤ off + A' by omega); omega
  · omega

theorem pwCz_some (m : OsMeta) (off n k z : Nat) (hz : m.zf = some z) :
    pwCz m off n k = if 0 < n ∧ k = n ∧ z ≤ off + n then max m.cz (pageEnd (off + n)) else m.cz := by
  unfold pwCz; rw [hz]

theorem pwCz_none (m : OsMeta) (off n k : Nat) (hz : m.zf = none) : pwCz m off n k = m.cz := by
  unfold pwCz; rw [hz]

/-- The cz of a next attempt: the last whole chunk's. -/
theorem pwCzE_step (m : OsMeta) (off A j E nn A' k : Nat) (hoff : off ≤ m.size) (hA0 : 0 < A)
    (hA : A ≤ A') (hnA : nn < A') (hE : E ≤ A') :
    pwCz (os.pwPostE m off A j E) (off + nn) (A' - nn) k =
      pwCz m off (if k = A' - nn then A' else E) (if k = A' - nn then A' else E) := by
  have hm1 : min off m.size = off := Nat.min_eq_left hoff
  have hz1 : (os.pwPostE m off A j E).zf = m.zf.map (fun z => max z (off + A)) := by
    simp only [os.pwPostE, pwPost, announce_zf, hm1]
    cases m.zf with
    | none => rfl
    | some z => simp only [Option.map_some, show off < off + A by omega, if_true]
  have hcz1 : (os.pwPostE m off A j E).cz = pwCz m off E E := rfl
  cases hzf : m.zf with
  | none =>
    rw [pwCz_none _ _ _ _ (by rw [hz1, hzf]; rfl), hcz1, pwCz_none _ _ _ _ hzf, pwCz_none _ _ _ _ hzf]
  | some z =>
    rw [pwCz_some _ _ _ _ (max z (off + A)) (by rw [hz1, hzf]; rfl), hcz1,
      show off + nn + (A' - nn) = off + A' by omega]
    by_cases hk : k = A' - nn
    · rw [if_pos hk, pwCz_some m off A' A' z hzf]
      by_cases hzA : z ≤ off + A'
      · rw [if_pos ⟨by omega, hk, by omega⟩, if_pos ⟨by omega, rfl, hzA⟩]
        have := pwCz_le_raise m off E A' hE z hzf hzA
        have := le_pwCz m off E E
        omega
      · rw [if_neg (by omega), if_neg (by omega), pwCz_some m off E E z hzf, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg hk]

/-- A write's next attempt, from `nn ≤ j` (where the last one stopped), announcing the chunk
`[off + nn, off + A')`, past what was announced (`A ≤ A'`): the `OsMeta` it leaves is the write's
that announced its first `A'` bytes, with the size the two leave, and the cz of its last whole
chunk. -/
theorem pwPostE_step (m : OsMeta) (off A j E nn A' k : Nat) (hoff : off ≤ m.size)
    (hlo : m.lo ≤ m.size) (hnn : nn ≤ j) (hj : j ≤ A) (hA0 : 0 < A) (hA : A ≤ A') (hnA : nn < A')
    (hk : k ≤ A' - nn) (hE : E ≤ j) :
    pwPost (os.pwPostE m off A j E) (off + nn) (A' - nn) k =
      os.pwPostE m off A' (max j (nn + k)) (if k = A' - nn then A' else E) := by
  have hS := pwSize_off m.size off j nn hoff hnn
  have hS2 := pwSize_le m.size off j A hj
  have hS3 := pwSize_ge m.size off j
  have hm1 : min off m.size = off := Nat.min_eq_left hoff
  have hsz : (os.pwPostE m off A j E).size = pwSize m.size off j := rfl
  apply os.osMeta_eq
  · show pwSize (os.pwPostE m off A j E).size (off + nn) k = pwSize m.size off (max j (nn + k))
    rw [hsz]; exact pwSize_from _ _ _ _ _ hnn
  · simp only [pwPost, os.pwPostE, announce_lo, hsz]; omega
  · simp only [pwPost, os.pwPostE, announce_hi]; omega
  · simp only [pwPost, os.pwPostE, announce_maps]
  · simp only [pwPost, os.pwPostE, announce_dlo, announce_dhi, os.touch_dlo, os.touch_dhi, hm1]
    by_cases h3 : m.dhi ≤ m.dlo <;>
      simp only [h3, if_true, if_false, show ¬ off + A ≤ off by omega,
        show ¬ off + A' ≤ off by omega] <;> (repeat' split) <;> omega
  · simp only [pwPost, os.pwPostE, announce_dlo, announce_dhi, os.touch_dlo, os.touch_dhi, hm1]
    by_cases h3 : m.dhi ≤ m.dlo <;>
      simp only [h3, if_true, if_false, show ¬ off + A ≤ off by omega,
        show ¬ off + A' ≤ off by omega] <;> (repeat' split) <;> omega
  · simp only [pwPost, os.pwPostE, announce_zf, Option.map_map, hm1]
    cases m.zf with
    | none => rfl
    | some z =>
      simp only [Option.map_some, Function.comp, Option.some.injEq,
        show off < off + A by omega, show off < off + A' by omega, if_true,
        show off + nn + (A' - nn) = off + A' by omega]
      (repeat' split) <;> omega
  · apply GMap.ext; intro b
    simp only [pwPost, os.pwPostE, announce_tc, hm1, inRange, Bool.and_eq_true,
      decide_eq_true_eq]
    (repeat' split) <;> first | rfl | omega
  · simp [pwPost, os.pwPostE]
  · exact pwCzE_step m off A j E nn A' k hoff hA0 hA hnA (by omega)
  · simp [pwPost, os.pwPostE]
  · -- the crash sizes known: a write inside the file keeps them, either way
    have hSu : pwSize m.size off j ≤ max m.size (off + j) := by unfold pwSize; split <;> omega
    have hSl : m.size ≤ pwSize m.size off j := by unfold pwSize; split <;> omega
    simp only [pwPost, os.pwPostE]
    (repeat' split) <;> first | rfl | omega


theorem wl_getD_lt {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem wl_getD_ge {α : Type} (l : List α) (i : Nat) (d : α) (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem wl_not_lt (off i j A' : Nat) (h1 : j ≤ A') (h2 : A' ≤ i) : ¬ off + i < off + j := by omega

/-- Before any attempt: the old bytes are a write's that announced and wrote nothing. -/
theorem pwOutA_zero (m : OsMeta) (off : Nat) (data : List w8) (xs : List ByteG)
    (hlen : xs.length = min (off + data.length) m.size - off) : os.PwOutA m off data 0 0 xs xs := by
  refine ⟨by simp [pwSize, hlen], fun i hi => ⟨?_, xs[i].2, [], by simp, fun h => absurd h (by omega),
    fun q hq => by simp at hq, fun _ => rfl⟩⟩
  unfold pwByte
  rw [if_neg (by omega), show off + i - off = i by omega, wl_getD_lt xs i _ hi]

set_option maxHeartbeats 1000000 in
/-- The bytes after a write's next attempt, from `nn ≤ j`, of the chunk `[nn, A')` (`A ≤ A'`), over
the bytes as a write that announced `A` and wrote `j` left them: the bytes before the chunk, the
attempt's, and the bytes after it, as a write that announced `A'` and wrote `max j (nn + k)`. -/
theorem pwOutA_step (m : OsMeta) (off nn : Nat) (data : List w8) (A j A' k nst : Nat)
    (xs ys : List ByteG) (zs : List Cands)
    (hoff : off ≤ m.size) (hnn : nn ≤ j) (hj : j ≤ A) (hA : A ≤ A') (hA' : A' ≤ data.length)
    (hnA : nn < A') (hk : k ≤ A' - nn)
    (hlen : xs.length = min (off + data.length) m.size - off)
    (hinv : os.PwOutA m off data A j xs ys) :
    os.PwOutA m off data A' (max j (nn + k)) xs
      (ys.take nn ++ pwBytes (pwSize m.size off j) (off + nn) ((data.drop nn).take (A' - nn)) k nst
        ((ys.drop nn).take (A' - nn)) zs ++ (ys.drop nn).drop (A' - nn)) := by
  obtain ⟨hyl, hel⟩ := hinv
  have hS := pwSize_off m.size off j nn hoff hnn
  have hS3 := pwSize_ge m.size off j
  have hpw := pwSize_from m.size off j nn k hnn
  have hxy : xs.length ≤ ys.length := by rw [hyl, hlen]; omega
  have hnny : nn ≤ ys.length := by rw [hyl]; omega
  have hjy : j ≤ ys.length := by
    rw [hyl]; unfold pwSize; split <;> omega
  have hdc : ((data.drop nn).take (A' - nn)).length = A' - nn := by
    simp only [List.length_take, List.length_drop]; omega
  have hy2 : ((ys.drop nn).take (A' - nn)).length = min (A' - nn) (ys.length - nn) := by
    simp only [List.length_take, List.length_drop]
  have hR : ((ys.drop nn).drop (A' - nn)).length = ys.length - nn - (A' - nn) := by
    simp only [List.length_drop]
  have hPl : (pwBytes (pwSize m.size off j) (off + nn) ((data.drop nn).take (A' - nn)) k nst
      ((ys.drop nn).take (A' - nn)) zs).length =
      min (off + nn + (A' - nn)) (pwSize m.size off (max j (nn + k))) - (off + nn) := by
    rw [pwBytes_length, hdc, hpw]
  have hS'1 : pwSize m.size off j ≤ pwSize m.size off (max j (nn + k)) := by
    rw [← hpw]; exact pwSize_ge _ _ _
  have hS'2 : pwSize m.size off (max j (nn + k)) ≤ max (pwSize m.size off j) (off + nn + k) := by
    rw [← hpw]; exact pwSize_le _ _ _ _ (Nat.le_refl _)
  unfold os.PwOutA
  clear hpw
  generalize pwSize m.size off (max j (nn + k)) = S' at *
  generalize pwSize m.size off j = S at *
  have hdi : ∀ i, nn ≤ i → i < A' → ((data.drop nn).take (A' - nn)).getD (i - nn) 0 = data.getD i 0 := by
    intro i h1 h2
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos (by omega), List.getElem?_drop, show nn + (i - nn) = i by omega]
  have hyi : ∀ i, nn ≤ i → i < A' → ((ys.drop nn).take (A' - nn)).getD (i - nn) (0, []) =
      ys.getD i (0, []) := by
    intro i h1 h2
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos (by omega), List.getElem?_drop, show nn + (i - nn) = i by omega]
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [List.length_append, List.length_take, Nat.min_eq_left hnny, hPl, hR]
    rcases Nat.lt_or_ge S (off + A') with h | h
    · have : ys.length ≤ nn + (A' - nn) := by rw [hyl]; omega
      omega
    · omega
  have hil := hi
  simp only [List.length_append, List.length_take, Nat.min_eq_left hnny, hPl, hR] at hil
  rw [List.getElem_append]
  split
  · rename_i hlt1
    rw [List.getElem_append]
    split
    · -- before the chunk
      rename_i hlt
      simp only [List.length_take, Nat.min_eq_left hnny] at hlt
      rw [List.getElem_take]
      obtain ⟨h1, c0, extra, h2, h3, h4, h5⟩ := hel i (by omega)
      refine ⟨?_, c0, extra, h2, fun _ => h3 (by omega), h4, h5⟩
      rw [h1]
      unfold pwByte
      rw [if_pos (show off + i < off + j by omega), if_pos (show off + i < off + max j (nn + k) by omega)]
    · -- the chunk
      rename_i hlt
      simp only [List.length_take, Nat.min_eq_left hnny, Nat.not_lt] at hlt
      simp only [List.length_append, List.length_take, Nat.min_eq_left hnny] at hlt1
      have hi2 : i - nn < (pwBytes S (off + nn) ((data.drop nn).take (A' - nn)) k nst
          ((ys.drop nn).take (A' - nn)) zs).length := by rw [hPl]; omega
      have hiA : i < A' := by rw [hPl] at hi2; omega
      simp only [List.length_take, Nat.min_eq_left hnny]
      refine ⟨?_, ?_⟩
      · rw [pwBytes_getElem _ _ _ _ _ _ _ _ hi2, show off + nn + (i - nn) = off + i by omega]
        unfold pwByte
        by_cases c2 : off + i < off + nn + k
        · rw [if_pos c2, if_pos (show off + i < off + max j (nn + k) by omega),
            show off + i - (off + nn) = i - nn by omega, hdi i hlt hiA, show off + i - off = i by omega]
        · rw [if_neg c2, show off + i - (off + nn) = i - nn by omega, hyi i hlt hiA]
          by_cases hiy : i < ys.length
          · rw [wl_getD_lt _ _ _ hiy, (hel i hiy).1]
            unfold pwByte
            by_cases c3 : off + i < off + j
            · rw [if_pos c3, if_pos (show off + i < off + max j (nn + k) by omega)]
            · rw [if_neg c3, if_neg (show ¬ off + i < off + max j (nn + k) by omega)]
          · rw [wl_getD_ge _ _ _ (by omega), if_neg (show ¬ off + i < off + max j (nn + k) by omega),
              show off + i - off = i by omega, wl_getD_ge xs _ _ (by omega)]
      · simp only [pwBytes, List.getElem_map, List.getElem_range]
        rw [hdi i hlt hiA]
        by_cases hiy : i < ys.length
        · rw [if_pos (show i - nn < ((ys.drop nn).take (A' - nn)).length by rw [hy2]; omega),
            hyi i hlt hiA, wl_getD_lt _ _ _ hiy]
          obtain ⟨-, c0, extra, h1, -, h3, h4⟩ := hel i hiy
          refine ⟨c0, extra ++ [(data.getD i 0, nst)], by rw [h1, List.append_assoc], fun _ => by simp,
            ?_, h4⟩
          intro q hq
          rcases List.mem_append.1 hq with hq | hq
          · exact h3 q hq
          · rw [List.mem_singleton] at hq; subst hq; rfl
        · rw [if_neg (show ¬ i - nn < ((ys.drop nn).take (A' - nn)).length by rw [hy2]; omega)]
          refine ⟨_, [(data.getD i 0, nst)], rfl, fun _ => by simp, fun q hq => by
            rw [List.mem_singleton] at hq; subst hq; rfl, fun h => absurd h (by omega)⟩
  · -- after the chunk
    rename_i hlt
    simp only [List.length_append, List.length_take, Nat.min_eq_left hnny, hPl, Nat.not_lt] at hlt
    have hRne : 0 < ys.length - nn - (A' - nn) := by omega
    have hP : min (off + nn + (A' - nn)) S' - (off + nn) = A' - nn := by
      have : off + A' ≤ S := by rw [hyl] at hRne; omega
      omega
    rw [List.getElem_drop, List.getElem_drop]
    simp only [List.length_append, List.length_take, Nat.min_eq_left hnny, hPl]
    have hidx : nn + (A' - nn + (i - (nn + (min (off + nn + (A' - nn)) S' - (off + nn))))) = i := by
      omega
    have hiy : i < ys.length := by omega
    simp only [hidx]
    obtain ⟨h1, c0, extra, h2, h3, h4, h5⟩ := hel i hiy
    refine ⟨?_, c0, extra, h2, fun h => absurd h (by omega), h4, h5⟩
    rw [h1]
    unfold pwByte
    have hiA' : A' ≤ i := by rw [hP] at hlt; omega
    have hij := wl_not_lt off i j A' (by omega) hiA'
    have hij' := wl_not_lt off i (max j (nn + k)) A' (by omega) hiA'
    rw [if_neg hij, if_neg hij']

/-- The bytes a write has landed after one more attempt, of the chunk `[nn, A')`, are a page cut or
the end of the last chunk that landed whole. -/
theorem pwCutE_step (off len nn j A A' E k : Nat) (hcj : os.PwCutE off len j E) (hnn : nn ≤ j)
    (hj : j ≤ A) (hA : A ≤ A') (hnA : nn < A') (hk : k ≤ A' - nn) (hjA : j = A → E = A)
    (hpc : PwCut (off + nn) (A' - nn) k) :
    os.PwCutE off len (max j (nn + k)) (if k = A' - nn then A' else E) := by
  unfold os.PwCutE PwCut at *
  obtain ⟨hpc1, hpc2⟩ := hpc
  by_cases hk' : k = A' - nn
  · rw [if_pos hk']
    by_cases hle : nn + k ≤ j
    · rw [Nat.max_eq_left hle]
      have h1 : j = A := by omega
      have h2 : A = A' := by omega
      have h3 : E = A' := by rw [hjA h1, h2]
      rw [← h3]; exact hcj
    · rw [Nat.max_eq_right (by omega)]
      right
      refine ⟨by omega, ?_⟩
      rcases hpc2 with h | h
      · omega
      · omega
  · rw [if_neg hk']
    by_cases hle : nn + k ≤ j
    · rw [Nat.max_eq_left hle]; exact hcj
    · rw [Nat.max_eq_right (by omega)]
      left
      refine ⟨?_, ?_⟩
      · rcases hpc1 with h | h | h
        · omega
        · exact absurd h hk'
        · right; right; rw [← Nat.add_assoc]; exact h
      · rcases hpc2 with h | h
        · omega
        · right; omega

/-- The bytes past a chunk are there only if the chunk is all below the size: then the attempt's
bytes are as many as it took. -/
theorem pwBytes_rest (S off nn c k nst len : Nat) (dc : List w8) (ys : List ByteG) (zs : List Cands)
    (hyl : ys.length = min (off + len) S - off) (hS : off + nn ≤ S) (hc : nn + c ≤ len)
    (hdc : dc.length = c) :
    (ys.drop nn).drop c = [] ∨
      ((ys.drop nn).take c).length = (pwBytes S (off + nn) dc k nst ((ys.drop nn).take c) zs).length := by
  rw [pwBytes_length, hdc]
  by_cases h : ys.length ≤ nn + c
  · left; apply List.drop_eq_nil_of_le; simp only [List.length_drop]; omega
  · right
    have := pwSize_ge S (off + nn) k
    simp only [List.length_take, List.length_drop]; omega

end lemmas

end EtcdGrove
end Perennial
