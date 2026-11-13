/-
The proof of `Spec/os/File__WriteAt.lean`: one attempt (`PWriteStart`, `PWriteFinish`) per
iteration of the model's loop, which retries only on `EINTR`, by Löb induction; the invariant is
the file as a write of the first `j` bytes left it (`pwPost_step`, `pwOut_step`).
-/
module

public import Proof.os.ErrorOk
public import Spec.os.File__WriteAt
public import Proof.os.WriteChunks

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
theorem pwCut_step (off len nn j k : Nat) (hj : PwCut off len j)
    (hnn : nn = 0 ∨ (off + nn) % osPageSize = 0) (hk : k ≤ len - nn) (hnl : nn < len)
    (hpc : PwCut (off + nn) (len - nn) k) : PwCut off len (max j (nn + k)) := by
  unfold PwCut at *
  unfold osPageSize at *
  rcases Nat.le_total j (nn + k) with h | h
  · rw [Nat.max_eq_right h]
    rcases hpc with h0 | h0 | h0
    · subst h0; rcases hnn with h1 | h1
      · left; omega
      · right; right; simpa using h1
    · right; left; omega
    · right; right; rw [← Nat.add_assoc]; exact h0
  · rw [Nat.max_eq_left h]; exact hj

/-- After a short attempt that succeeded, the next starts on a page boundary. -/
theorem pwCut_short (off len nn k : Nat) (hk0 : 0 < k) (hfull : nn + k ≠ len)
    (hpc : PwCut (off + nn) (len - nn) k) (hk : k ≤ len - nn) :
    nn + k = 0 ∨ (off + (nn + k)) % osPageSize = 0 := by
  unfold PwCut at hpc
  rcases hpc with h0 | h0 | h0
  · omega
  · omega
  · right; rw [← Nat.add_assoc]; exact h0

theorem os.File.WriteAt.wp_proof : os.File.WriteAt.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d m xs hwr hoff hgap hbig hn hn2 hxl
  have hmin0 : min off.toNat m.size = off.toNat := Nat.min_eq_left hgap
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hm, Hbs, Hc⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl dqs data $$ Hsl with %Hlen
  icases ownSlice_wf sl dqs data $$ Hsl with %Hwf
  wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_auto
  have hl0 : sl.len ≠ W64 0 := by
    intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; omega
  rw [decide_eq_false hl0]
  wp_pure
  wp_pure
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  -- the invariant: the file as a write of the first `j` bytes left it, `nn ≤ j` of them written
  obtain ⟨nnv, hnnv⟩ : ∃ nnv : w64, nnv = W64 0 := ⟨_, rfl⟩
  conv in (occs := 4) (#(W64 0) : val) => rw [← hnnv]
  obtain ⟨mj, hmj⟩ : ∃ mj, mj = m := ⟨_, rfl⟩
  ihave Hm := (show osMeta (GF := GF) d.ino (DFrac.own 1) m ⊢ osMeta d.ino (DFrac.own 1) mj by
    rw [hmj]) $$ Hm
  obtain ⟨ys, hy⟩ : ∃ ys, ys = xs := ⟨_, rfl⟩
  ihave Hbs := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own 1) xs ⊢
    osBytes d.ino off.toNat (DFrac.own 1) ys by rw [hy]) $$ Hbs
  generalize hj0 : (0 : Nat) = j
  have hj : j ≤ data.length := by omega
  have hnn : nnv.toNat ≤ j := by subst hnnv; rw [← hj0]; decide
  have hnl : nnv.toNat < data.length := by
    subst hnnv; have : (W64 0).toNat = 0 := rfl
    omega
  have hinv : (j = 0 ∧ nnv.toNat = 0 ∧ mj = m ∧ ys = xs) ∨
      (mj = pwPost m off.toNat data.length j ∧ os.PwOut m off.toNat data j xs ys) :=
    .inl ⟨hj0.symm, by subst hnnv; rfl, hmj, hy⟩
  have hcj : PwCut off.toNat data.length j := by unfold PwCut; left; exact hj0.symm
  have hcn : nnv.toNat = 0 ∨ (off.toNat + nnv.toNat) % osPageSize = 0 := by
    left; subst hnnv; rfl
  clear hmj hy hj0 hnnv
  iloeb as IH generalizing %j %nnv %mj %ys %hnn %hnl %hj %hinv %hcj %hcn Hm Hbs Hc Hosfd Hsl Hfd HΦ
  -- one attempt, from `nn`
  have hnnz : sint.Z nnv = nnv.toNat := by
    simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  have hnnn : sint.nat nnv = nnv.toNat := by simp [sint.nat, hnnz]
  wp_auto
  have hmax : ¬ (sint.Z (W64 1073741824) < sint.Z (sl.len - nnv)) := by
    have hsub : sint.Z (sl.len - nnv) = sint.Z sl.len - sint.Z nnv := by
      have : sint.Z nnv ≤ sint.Z sl.len := by rw [hnnz, hslz]; omega
      have : 0 ≤ sint.Z nnv := by rw [hnnz]; omega
      word
    rw [hsub, hslz, hnnz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
  rw [decide_eq_false hmax]
  wp_auto
  have hsb : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
    rw [hnnz, hslz]; omega
  rw [if_pos hsb]
  ihave ⟨Hsl1, Hsl2⟩ := (ownSlice_split_all nnv sl dqs data ⟨by omega, by omega⟩).1 $$ Hsl
  rw [hnnn]
  wp_apply wp_bytes_to_string _ (data.drop nnv.toNat) dqs $$ Hsl2 as Hsl2
  ihave Hsl := (ownSlice_split_all nnv sl dqs data ⟨by omega, by omega⟩).2 $$ [Hsl1 Hsl2]
  · rw [hnnn]; iframe
  -- the bytes and cells this attempt takes
  have hmsz : mj.size = pwSize m.size off.toNat j := by
    rcases hinv with ⟨rfl, -, rfl, -⟩ | ⟨rfl, -⟩
    · simp [pwSize]
    · rfl
  have hmaps : mj.maps = m.maps := by
    rcases hinv with ⟨-, -, rfl, -⟩ | ⟨rfl, -⟩ <;> simp [pwPost]
  have hyl : ys.length = min (off.toNat + data.length) (pwSize m.size off.toNat j) - off.toNat := by
    rcases hinv with ⟨rfl, -, -, rfl⟩ | ⟨-, h⟩
    · simp [pwSize, hxl]
    · exact h.1
  have hS := pwSize_off m.size off.toNat j nnv.toNat hgap hnn
  have hnny : nnv.toNat ≤ ys.length := by rw [hyl]; omega
  ihave ⟨Hbs1, Hbs2⟩ := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own 1) ys ⊢
      osBytes d.ino off.toNat (DFrac.own 1) (ys.take nnv.toNat) ∗
      osBytes d.ino (off.toNat + nnv.toNat) (DFrac.own 1) (ys.drop nnv.toNat) by
    conv => lhs; rw [← List.take_append_drop nnv.toNat ys]
    unfold osBytes
    refine (bytesG_append _ _ _ _ _ _).1.trans ?_
    rw [List.length_take, Nat.min_eq_left hnny]) $$ Hbs
  ihave ⟨Hc1, Hc2⟩ := mcellsAny_split m.maps off.toNat (off.toNat + nnv.toNat)
    (off.toNat + data.length) (by omega) (by omega) $$ Hc
  have hoffv : (off + nnv).toNat = off.toNat + nnv.toNat := by
    rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
  have hoffv' : 0 ≤ (off + nnv).toInt := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hoffv]; omega)]; omega
  have hminS : min (off.toNat + nnv.toNat) (pwSize m.size off.toNat j) = off.toNat + nnv.toNat :=
    Nat.min_eq_left hS
  have hdl : (data.drop nnv.toNat).length = data.length - nnv.toNat := List.length_drop
  have hdne : data.drop nnv.toNat ≠ [] := by
    intro h; have := congrArg List.length h; rw [hdl] at this; simp at this; omega
  have hend : off.toNat + nnv.toNat + (data.length - nnv.toNat) = off.toNat + data.length := by
    omega
  wp_apply wp_osPWriteStart fd (off + nnv) (data.drop nnv.toNat) dq d mj (ys.drop nnv.toNat)
    CoPset.subseteq_top hwr hoffv' (by rw [hoffv, hmsz]; exact hS) hdne
    (by rw [hoffv, hdl, List.length_drop, hyl, hmsz, hend]; omega)
    $$ Hinv Hosfd Hm [Hbs2] [Hc2] as %t %nst %- Hosfd Ht
  · rw [hoffv]; iexact Hbs2
  · rw [hoffv, hdl, hend, hmaps]; iexact Hc2
  wp_apply wp_osPWriteFinish t d.ino (off + nnv).toNat (data.drop nnv.toNat) mj
    (ys.drop nnv.toNat) nst CoPset.subseteq_top $$ Hinv Ht as %k %e %zs %hke %hpc Hm Hbs2 Hc2
  obtain ⟨hk, hke, -, -⟩ := hke
  rw [hdl] at hk
  have hpc' : PwCut (off.toNat + nnv.toNat) (data.length - nnv.toNat) k := by
    rw [hoffv, hdl] at hpc; exact hpc
  have hcj' : PwCut off.toNat data.length (max j (nnv.toNat + k)) :=
    pwCut_step _ _ _ _ _ hcj hcn hk hnl hpc'
  -- the file as a write of the first `max j (nn + k)` bytes left it
  have hmeta : pwPost mj (off + nnv).toNat (data.drop nnv.toNat).length k =
      pwPost m off.toNat data.length (max j (nnv.toNat + k)) := by
    rw [hoffv, hdl]
    rcases hinv with ⟨rfl, h0, rfl, -⟩ | ⟨rfl, -⟩
    · rw [h0]; simp
    · exact pwPost_step m off.toNat data.length nnv.toNat j k hgap hnn hj hnl hk
  ihave Hm := (show osMeta (GF := GF) d.ino (DFrac.own 1)
      (pwPost mj (off + nnv).toNat (data.drop nnv.toNat).length k) ⊢
    osMeta d.ino (DFrac.own 1) (pwPost m off.toNat data.length (max j (nnv.toNat + k)))
      by rw [hmeta]) $$ Hm
  ihave Hbs := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own 1) (ys.take nnv.toNat) ∗
      osBytes d.ino (off + nnv).toNat (DFrac.own 1)
        (pwBytes mj.size (off + nnv).toNat (data.drop nnv.toNat) k nst (ys.drop nnv.toNat) zs) ⊢
      osBytes d.ino off.toNat (DFrac.own 1)
        (ys.take nnv.toNat ++ pwBytes (pwSize m.size off.toNat j) (off.toNat + nnv.toNat)
          (data.drop nnv.toNat) k nst (ys.drop nnv.toNat) zs) by
    rw [hoffv, hmsz]
    unfold osBytes
    refine BIBase.Entails.trans ?_ (bytesG_append _ _ _ _ _ _).2
    rw [List.length_take, Nat.min_eq_left hnny]) $$ [Hbs1 Hbs2]
  · iframe
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc := mcellsAny_merge m.maps off.toNat (off.toNat + nnv.toNat) (off.toNat + data.length)
    (by omega) (by omega) $$ [Hc1 Hc2]
  · rw [hoffv, hdl, hend, hmaps]; iframe
  have hys' := pwOut_step m off.toNat nnv.toNat data j k nst xs ys zs hgap hnn hj hk hxl
    (by rcases hinv with ⟨h1, h2, -, h3⟩ | ⟨-, h⟩
        · exact .inl ⟨h1, h2, h3⟩
        · exact .inr h)
  have hj' : max j (nnv.toNat + k) ≤ data.length := by omega
  have hsln : sl.len = W64 data.length := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.Z] at hslz
    rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %(max j (nnv.toNat + k)) %nnv %_ %_ %(by omega) %hnl %hj' %(.inr ⟨rfl, hys'⟩)
      %hcj' %hcn Hm Hbs Hc Hosfd Hsl Hfd HΦ
  · rw [decide_eq_false he4]
    wp_auto
    have hWk : (W64 k).toNat = k := by
      simp only [W64]; rw [BitVec.toNat_ofInt]; omega
    have hnk : (nnv + W64 k).toNat = nnv.toNat + k := by
      rw [BitVec.toNat_add, hWk]; exact Nat.mod_eq_of_lt (by omega)
    by_cases hfull : nnv + W64 k = sl.len
    · rw [decide_eq_true hfull]
      wp_auto
      have hfk : nnv.toNat + k = data.length := by
        have := congrArg BitVec.toNat hfull; rw [hnk, hsln] at this
        simp only [W64] at this; rw [BitVec.toNat_ofInt] at this; omega
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        wp_auto
        ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hj', hys', hcj', .inl ⟨by omega, hsln, rfl⟩⟩
      · rw [decide_eq_false he0]
        wp_auto
        simp only [decide_eq_false he0, Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0 $$ Hn as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hj', hys', hcj', .inr ⟨rfl, by intro h; cases h⟩⟩
    · rw [decide_eq_false hfull]
      wp_auto
      by_cases he0 : e = W64 0
      · -- a short write: the next attempt from `nn + k`
        rw [decide_eq_true he0]
        simp only [Bool.not_true]
        wp_pure
        have hk0 : 0 < k := by
          rcases hke with ⟨hkk | hkk, -⟩ | hne
          · have : nnv.toNat + k ≠ data.length := by
              intro hc; apply hfull; apply BitVec.eq_of_toNat_eq
              rw [hnk, hsln]; simp only [W64]; rw [BitVec.toNat_ofInt]; omega
            omega
          · exact hkk
          · exact absurd he0 hne
        have hnl' : (nnv + W64 k).toNat < data.length := by
          rw [hnk]
          have : nnv.toNat + k ≠ data.length := by
            intro hc; apply hfull; apply BitVec.eq_of_toNat_eq
            rw [hnk, hsln]; simp only [W64]; rw [BitVec.toNat_ofInt]; omega
          omega
        have hcn' : (nnv + W64 k).toNat = 0 ∨ (off.toNat + (nnv + W64 k).toNat) % osPageSize = 0 := by
          rw [hnk]
          exact pwCut_short _ _ _ _ hk0 (by rw [hnk] at hnl'; omega) hpc' hk
        iapply IH $$ %(max j (nnv.toNat + k)) %(nnv + W64 k) %_ %_ %(by rw [hnk]; omega) %hnl'
          %hj' %(.inr ⟨rfl, hys'⟩) %hcj' %hcn' [Hm] [Hbs] [Hc] Hosfd Hsl Hfd HΦ
        · iexact Hm
        · iexact Hbs
        · iexact Hc
      · rw [decide_eq_false he0]
        simp only [Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0 $$ Hn as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hj', hys', hcj', .inr ⟨rfl, by intro h; cases h⟩⟩

/-! ## Any write: past the end of the file, and in chunks of at most 1 GiB -/

theorem wa_wp_call1_gen (F : val) (n0 : w64) (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n = n0⌝ -∗ WP (App (Val F) (Val #n)) {{ Φ }}) ⊢
    WP (App (Val F) (Val #n0)) {{ Φ }} := by
  iintro H
  iapply H
  ipureintro; rfl

theorem wa_sintZ_W64 (x : Nat) (h : x < 2 ^ 63) : sint.Z (W64 x) = x := by
  simp only [sint.Z, W64]; rw [BitVec.toInt_ofInt, Int.bmod]; split <;> omega

theorem wa_sintNat_W64 (x : Nat) (h : x < 2 ^ 63) : sint.nat (W64 x) = x := by
  simp only [sint.nat]; rw [show (W64 x).toInt = x from wa_sintZ_W64 x h]; simp

theorem wa_W64_add (a b : Nat) : W64 a + W64 b = W64 (a + b : Nat) := by
  show BitVec.ofInt 64 (a : Int) + BitVec.ofInt 64 (b : Int) = BitVec.ofInt 64 ((a + b : Nat) : Int)
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem wa_W64_sub (a b : Nat) (_ha : a < 2 ^ 63) (h : b ≤ a) :
    W64 a - W64 b = W64 (a - b : Nat) := by
  show BitVec.ofInt 64 (a : Int) - BitVec.ofInt 64 (b : Int) = BitVec.ofInt 64 ((a - b : Nat) : Int)
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem wa_W64_inj (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    W64 a = W64 b ↔ a = b := by
  constructor
  · intro h; have := congrArg sint.Z h; rw [wa_sintZ_W64 a ha, wa_sintZ_W64 b hb] at this; omega
  · intro h; rw [h]

theorem wa_toNat_add_W64 (off : w64) (nn : Nat) (h : off.toNat + nn < 2 ^ 63) :
    (off + W64 nn).toNat = off.toNat + nn := by
  rw [BitVec.toNat_add]
  have : (W64 nn).toNat = nn := by
    simp only [W64]; rw [BitVec.toNat_ofInt]; omega
  rw [this]; exact Nat.mod_eq_of_lt (by omega)

/-- The bytes a write has landed after one more attempt, of the chunk `c` from `nn`, are a cut. -/
theorem waCut_step (off len nn j c k : Nat) (hj : os.WaCut off len j)
    (hcn : (off + nn) % osPageSize = 0 ∨ nn % 0x40000000 = 0)
    (hc : c = min (len - nn) 0x40000000) (hk : k ≤ c) (hnl : nn < len)
    (hpc : PwCut (off + nn) c k) : os.WaCut off len (max j (nn + k)) := by
  unfold os.WaCut PwCut at *
  unfold osPageSize at *
  rcases Nat.le_total j (nn + k) with h | h
  · rw [Nat.max_eq_right h]
    rcases hpc with h0 | h0 | h0
    · subst h0; rcases hcn with h1 | h1
      · left; right; right; simpa using h1
      · right; simpa using h1
    · by_cases hcl : len - nn ≤ 0x40000000
      · left; right; left; omega
      · rcases hcn with h1 | h1
        · left; right; right; omega
        · right; omega
    · left; right; right; rw [← Nat.add_assoc]; exact h0
  · rw [Nat.max_eq_left h]; exact hj

/-- After an attempt that wrote some of its chunk and succeeded, the next starts on a page boundary
or a chunk boundary. -/
theorem waCut_short (off len nn c k : Nat)
    (hcn : (off + nn) % osPageSize = 0 ∨ nn % 0x40000000 = 0)
    (hc : c = min (len - nn) 0x40000000) (hk0 : 0 < k) (hfull : nn + k ≠ len) (hk : k ≤ c)
    (hnl : nn < len) (hpc : PwCut (off + nn) c k) :
    (off + (nn + k)) % osPageSize = 0 ∨ (nn + k) % 0x40000000 = 0 := by
  unfold PwCut osPageSize at *
  rcases hpc with h0 | h0 | h0
  · omega
  · rcases hcn with h1 | h1
    · left; omega
    · right; omega
  · left; rw [← Nat.add_assoc]; exact h0

set_option maxHeartbeats 2000000 in
theorem os.File.WriteAt.wp_proofExt : os.File.WriteAt.specExt (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d m xs hwr hoff hbig hn hxl
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hm, Hbs, Hc⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl dqs data $$ Hsl with %Hlen
  icases ownSlice_wf sl dqs data $$ Hsl with %Hwf
  wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_auto
  have hl0 : sl.len ≠ W64 0 := by
    intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; omega
  rw [decide_eq_false hl0]
  wp_pure
  wp_pure
  iapply wa_wp_call1_gen
  iintro %nw %hnw
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  have hsln : sl.len = W64 data.length := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.Z] at hslz
    rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
  obtain ⟨nn, hnn0⟩ : ∃ nn : Nat, nn = 0 := ⟨_, rfl⟩
  have hnw' : nw = W64 nn := by rw [hnw, hnn0]; rfl
  clear hnw
  -- the invariant: the file as a write of the first `j ≥ nn` bytes left it, whose attempts
  -- announced `[min off size, off + a)`
  obtain ⟨j, hj0⟩ : ∃ j : Nat, j = 0 := ⟨_, rfl⟩
  obtain ⟨a, ha0⟩ : ∃ a : Nat, a = 0 := ⟨_, rfl⟩
  obtain ⟨mj, hmj⟩ : ∃ mj, mj = m := ⟨_, rfl⟩
  ihave Hm := (show osMeta (GF := GF) d.ino (DFrac.own 1) m ⊢ osMeta d.ino (DFrac.own 1) mj by
    rw [hmj]) $$ Hm
  obtain ⟨ys, hy⟩ : ∃ ys, ys = xs := ⟨_, rfl⟩
  ihave Hbs := (show osBytes (GF := GF) d.ino (min off.toNat m.size) (DFrac.own 1) xs ⊢
    osBytes d.ino (min off.toNat m.size) (DFrac.own 1) ys by rw [hy]) $$ Hbs
  have hj : j ≤ data.length := by omega
  have hnj : nn ≤ j := by omega
  have hnl : nn < data.length := by omega
  have hys : ys.map Prod.fst = pwValsG m.size off.toNat data j xs := by
    rw [hy, hj0, pwValsG_zero _ _ _ _ hxl]
  have hinv : (j = 0 ∧ nn = 0 ∧ mj = m) ∨
      (mj = pwPost m off.toNat a j ∧ m.lo ≤ m.size ∧ j ≤ a ∧ a ≤ data.length ∧
        min data.length 0x40000000 ≤ a ∧ a ≤ nn + 0x40000000 ∧ 0 < a) :=
    .inl ⟨hj0, hnn0, hmj⟩
  have hcj : os.WaCut off.toNat data.length j := by
    unfold os.WaCut PwCut; left; left; exact hj0
  have hcn : (off.toNat + nn) % osPageSize = 0 ∨ nn % 0x40000000 = 0 := by
    right; rw [hnn0]
  clear hmj hy hj0 hnn0 ha0
  iloeb as IH generalizing %nw %nn %j %a %mj %ys %hnw' %hj %hnj %hnl %hys %hinv %hcj %hcn
    Hm Hbs Hc Hosfd Hsl Hfd HΦ
  subst hnw'
  -- one attempt, of the chunk `[nn, nn + c)`
  have hmsz : mj.size = pwSize m.size off.toNat j := by
    rcases hinv with ⟨rfl, -, rfl⟩ | ⟨rfl, -⟩
    · simp [pwSize]
    · rfl
  have hmaps : mj.maps = m.maps := by
    rcases hinv with ⟨-, -, rfl⟩ | ⟨rfl, -⟩ <;> simp [pwPost]
  wp_auto
  have hlZ : sint.Z (sl.len - W64 ↑nn) = ↑(data.length - nn) := by
    rw [hsln, wa_W64_sub _ _ (by omega) (by omega), wa_sintZ_W64 _ (by omega)]
  have h30 : sint.Z (W64 1073741824) = 1073741824 := rfl
  obtain ⟨c, hcdef⟩ : ∃ c, c = min (data.length - nn) 1073741824 := ⟨_, rfl⟩
  have hcn' : nn + c ≤ data.length := by omega
  have hc0 : 0 < c := by omega
  wp_join (Q := fun v => iprop(⌜v = #(W64 ↑(nn + c))⌝)) at (if: _ then _ else _) with [] as %Hv
  · by_cases hbig' : 1073741824 < data.length - nn
    · rw [decide_eq_true (by rw [hlZ, h30]; omega)]
      wp_auto
      ipureintro
      rw [show (1073741824 : Int) = ((1073741824 : Nat) : Int) from rfl, wa_W64_add]
      congr 3; omega
    · rw [decide_eq_false (by rw [hlZ, h30]; omega)]
      wp_auto
      ipureintro
      rw [hsln]; congr 3; omega
  subst Hv
  wp_auto
  have hsb : 0 ≤ sint.Z (W64 ↑nn) ∧ sint.Z (W64 ↑nn) ≤ sint.Z (W64 ↑(nn + c)) ∧
      sint.Z (W64 ↑(nn + c)) ≤ sint.Z sl.cap := by
    rw [wa_sintZ_W64 _ (by omega), wa_sintZ_W64 _ (by omega)]; omega
  rw [if_pos hsb]
  have hsb2 : 0 ≤ sint.Z (W64 ↑nn) ∧ sint.Z (W64 ↑nn) ≤ sint.Z (W64 ↑(nn + c)) ∧
      sint.Z (W64 ↑(nn + c)) ≤ sint.Z sl.len := by
    rw [wa_sintZ_W64 _ (by omega), wa_sintZ_W64 _ (by omega)]; omega
  icases (ownSlice_slice (W64 ↑nn) (W64 ↑(nn + c)) sl dqs data hsb2).1 $$ Hsl with
    ⟨Hsl1, Hsl2, Hsl3⟩
  wp_apply wp_bytes_to_string _ _ dqs $$ Hsl2 as Hsl2
  ihave Hsl := (ownSlice_slice (W64 ↑nn) (W64 ↑(nn + c)) sl dqs data hsb2).2 $$ [Hsl1 Hsl2 Hsl3]
  · iframe
  generalize hcd0 : subslice (sint.nat (W64 ↑nn)) (sint.nat (W64 ↑(nn + c))) data = cd
  have hcd : cd = (data.drop nn).take c := by
    rw [← hcd0, wa_sintNat_W64 _ (by omega), wa_sintNat_W64 _ (by omega)]
    simp only [subslice, List.drop_take]; congr 1; omega
  have hcdl : cd.length = c := by rw [hcd]; simp; omega
  have hcdne : cd ≠ [] := by intro h; rw [h] at hcdl; simp at hcdl; omega
  clear hcd0
  have hocN : (off + W64 ↑nn).toNat = off.toNat + nn := wa_toNat_add_W64 off nn (by omega)
  have hocI : 0 ≤ (off + W64 ↑nn).toInt := by
    have := BitVec.toInt_eq_toNat_cond (off + W64 ↑nn); split at this <;> omega
  generalize hoc : off + W64 ↑nn = oc at hocN hocI ⊢
  -- the bytes and cells the attempt takes
  have hyl : ys.length = min (off.toNat + data.length) (pwSize m.size off.toNat j) -
      min off.toNat m.size := by
    have := congrArg List.length hys; simp only [List.length_map, pwValsG_length] at this; exact this
  have hsz : m.size ≤ pwSize m.size off.toNat j := by unfold pwSize; split <;> omega
  icases osBytes_split3_range d.ino (min off.toNat m.size) (min oc.toNat (pwSize m.size off.toNat j))
      (min (oc.toNat + c) (pwSize m.size off.toNat j)) (DFrac.own 1) ys
      (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min off.toNat m.size)
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))
      (by omega) (by omega) (by omega) (by omega) (by omega) $$ Hbs with ⟨Hbs1, Hbs2, Hbs3⟩
  icases mcellsAny_split m.maps (min off.toNat m.size) (min oc.toNat (pwSize m.size off.toNat j))
    (off.toNat + data.length) (by omega) (by omega) $$ Hc with ⟨Hc1, Hc23⟩
  icases mcellsAny_split m.maps (min oc.toNat (pwSize m.size off.toNat j)) (oc.toNat + cd.length)
    (off.toNat + data.length) (by omega) (by omega) $$ Hc23 with ⟨Hc2, Hc3⟩
  ihave Hbs2 := (show osBytes (GF := GF) d.ino (min oc.toNat (pwSize m.size off.toNat j))
      (DFrac.own 1) ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
        (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))) ⊢
      osBytes d.ino (min oc.toNat mj.size) (DFrac.own 1)
        ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
          (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))) by
    rw [hmsz]) $$ Hbs2
  ihave Hc2 := (show mcellsAny (GF := GF) m.maps (min oc.toNat (pwSize m.size off.toNat j))
      (oc.toNat + cd.length) ⊢ mcellsAny mj.maps (min oc.toNat mj.size) (oc.toNat + cd.length) by
    rw [hmsz, hmaps]) $$ Hc2
  wp_apply wp_osPWriteStartG fd oc cd dq d mj
    ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
    CoPset.subseteq_top hwr hocI hcdne (by
      simp only [List.length_take, List.length_drop, hcdl, hmsz]
      omega)
    $$ Hinv Hosfd Hm Hbs2 Hc2 as %t %nst %hst Hosfd Ht
  have hmlo : mj.lo ≤ mj.size := hst.2.2.2
  wp_apply wp_osPWriteFinishG t d.ino oc.toNat cd mj
    ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
    nst CoPset.subseteq_top $$ Hinv Ht as %k %e %zs %hke %hpc Hm Hbs2 Hc2
  obtain ⟨hk, hke, -, -⟩ := hke
  rw [hcdl] at hk
  rw [hcdl, hocN] at hpc
  -- the file as a write of the first `max j (nn + k)` bytes left it, announced up to `nn + c`
  have hml : m.lo ≤ m.size := by
    rcases hinv with ⟨-, -, rfl⟩ | ⟨-, h, -⟩
    · exact hmlo
    · exact h
  have hmeta : pwPost mj oc.toNat cd.length k = pwPost m off.toNat (nn + c) (max j (nn + k)) := by
    rw [hcdl, hocN]
    rcases hinv with ⟨rfl, rfl, rfl⟩ | ⟨rfl, -, hja, hal, -, ha, ha0⟩
    · simp
    · exact pwPost_chunk m off.toNat a nn j c k hml hnj hja (by omega) ha0 hk hc0
  ihave Hm := (show osMeta (GF := GF) d.ino (DFrac.own 1) (pwPost mj oc.toNat cd.length k) ⊢
    osMeta d.ino (DFrac.own 1) (pwPost m off.toNat (nn + c) (max j (nn + k))) by
      rw [hmeta]) $$ Hm
  have hL2 := pwBytesG_length mj.size oc.toNat cd k nst
    ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))) zs
  rw [hcdl] at hL2
  have hend := pwChunk_end (pwSize m.size off.toNat j) off.toNat data.length nn c k
    (min off.toNat m.size) ys hk hcn' hyl
  rw [← hocN] at hend
  ihave Hbs := osBytes_app3 d.ino (min off.toNat m.size) (min oc.toNat (pwSize m.size off.toNat j))
    (min (oc.toNat + c) (pwSize m.size off.toNat j)) (DFrac.own 1)
    (ys.take (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size))
    (pwBytesG mj.size oc.toNat cd k nst
      ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
        (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
      zs)
    (ys.drop (min (oc.toNat + c) (pwSize m.size off.toNat j) - min off.toNat m.size))
    (by simp only [List.length_take]; omega)
    (by rw [hL2, hmsz]; rcases hend with h1 | h1
        · left; omega
        · right; exact h1) $$ [Hbs1 Hbs2 Hbs3]
  · rw [hmsz]; iframe
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc23 := mcellsAny_merge m.maps (min oc.toNat (pwSize m.size off.toNat j))
    (oc.toNat + cd.length) (off.toNat + data.length) (by omega) (by omega) $$ [Hc2 Hc3]
  · rw [hmsz, hmaps]; iframe
  ihave Hc := mcellsAny_merge m.maps (min off.toNat m.size)
    (min oc.toNat (pwSize m.size off.toNat j)) (off.toNat + data.length) (by omega) (by omega)
    $$ [Hc1 Hc23]
  · iframe
  have hys' := pwValsG_chunk m.size off.toNat data cd j nn c k xs ys
    (pwBytesG mj.size oc.toNat cd k nst
      ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
        (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
      zs) hnj hj hcn' hk hcd hxl hys
    (by rw [pwBytesG_map_fst, hmsz, hocN])
  rw [← hocN] at hys'
  have hJ : max j (nn + k) ≤ data.length := by omega
  have hnJ : nn ≤ max j (nn + k) := by omega
  have hcj' : os.WaCut off.toNat data.length (max j (nn + k)) :=
    waCut_step _ _ _ _ _ _ hcj hcn hcdef hk hnl hpc
  have hA : max j (nn + k) ≤ nn + c ∧ nn + c ≤ data.length ∧
      min data.length 0x40000000 ≤ nn + c ∧ 0 < nn + c := by omega
  have hinv' : ∀ nn', nn ≤ nn' → (max j (nn + k) = 0 ∧ nn' = 0 ∧
      pwPost m off.toNat (nn + c) (max j (nn + k)) = m) ∨
      (pwPost m off.toNat (nn + c) (max j (nn + k)) = pwPost m off.toNat (nn + c) (max j (nn + k)) ∧
        m.lo ≤ m.size ∧ max j (nn + k) ≤ nn + c ∧ nn + c ≤ data.length ∧
        min data.length 0x40000000 ≤ nn + c ∧ nn + c ≤ nn' + 0x40000000 ∧ 0 < nn + c) :=
    fun nn' h => .inr ⟨rfl, hml, hA.1, hA.2.1, hA.2.2.1, by omega, hA.2.2.2⟩
  clear hend hL2 hyl hsz hlZ hsb hsb2 hys hcd hslz Hlen Hwf hinv hmeta hmsz hmaps
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %(W64 ↑nn) %nn %(max j (nn + k)) %(nn + c) %_ %_ %rfl %hJ %hnJ %hnl %hys'
      %(hinv' nn (Nat.le_refl _)) %hcj' %hcn Hm Hbs Hc Hosfd Hsl Hfd HΦ
  · rw [decide_eq_false he4]
    wp_auto
    rcases hke with ⟨hkc', rfl⟩ | he0
    · by_cases hfull : nn + k = data.length
      · rw [decide_eq_true (show W64 ↑nn + W64 ↑k = sl.len by
          rw [wa_W64_add, hsln]; congr 2)]
        wp_auto
        ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hA.1, hA.2.1, hA.2.2.1, hys', hcj', .inl ⟨by omega, hsln, rfl⟩⟩
      · rw [decide_eq_false (show ¬ W64 ↑nn + W64 ↑k = sl.len by
          rw [wa_W64_add, hsln, wa_W64_inj _ _ (by omega) (by omega)]; omega)]
        wp_pure
        wp_pure
        wp_pure
        wp_pure
        wp_pure
        wp_pure
        wp_pure
        have hk0 : 0 < k := by
          rcases hkc' with h | h
          · omega
          · exact h
        have hnw2 : W64 ↑nn + W64 ↑k = W64 ↑(nn + k) := wa_W64_add nn k
        have hnJ2 : nn + k ≤ max j (nn + k) := by omega
        have hnl2 : nn + k < data.length := by omega
        have hcn2 := waCut_short _ _ _ _ _ hcn hcdef hk0 hfull hk hnl hpc
        iapply IH $$ %(W64 ↑nn + W64 ↑k) %(nn + k) %(max j (nn + k)) %(nn + c) %_ %_
          %hnw2 %hJ %hnJ2 %hnl2 %hys' %(hinv' (nn + k) (by omega)) %hcj' %hcn2
          Hm Hbs Hc Hosfd Hsl Hfd HΦ
    · have he0' : ¬ e = W64 0 := he0
      by_cases hkl : W64 ↑nn + W64 ↑k = sl.len
      · rw [decide_eq_true hkl]
        wp_auto
        rw [decide_eq_false he0']
        wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hA.1, hA.2.1, hA.2.2.1, hys', hcj', .inr ⟨rfl, by intro h; cases h⟩⟩
      · rw [decide_eq_false hkl]
        wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hA.1, hA.2.1, hA.2.2.1, hys', hcj', .inr ⟨rfl, by intro h; cases h⟩⟩

end proof

end EtcdGrove
end Perennial
