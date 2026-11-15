/-
The proof of `os.File.WriteAt.specExt` (`Spec/os/File__WriteAt.lean`): any write, past the end of the
file and in chunks of at most 1 GiB (`Proof/os/WriteChunks.lean`). Split from `File__WriteAt.lean`
(2026-11-15, notes/wal-lean-integration.md), so that the WAL's proofs, which use `specLong`
(`Proof/os/WriteLong.lean`), do not wait on it: under the per-byte extension's page cache known zero
(`OsMeta.cz`, raised by a write that lands whole, `pwCz`) its post `pwPost m off a j` is not the state
a chunked write leaves (`WriteChunks.pwPost_chunk`'s `cz` goal), to be restated as `specLong`'s
(`os.pwPostE`): see notes/wal-lean-integration.md, "Open: `specExt` under `cz`".
-/
module

public import Proof.os.File__WriteAt
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
theorem waCut_step (off len nn j c k : Nat) (hj0 : os.WaCut off len j)
    (hcn : (off + nn) % osPageSize = 0 ∨ nn % 0x40000000 = 0)
    (hc : c = min (len - nn) 0x40000000) (hk : k ≤ c) (hnl : nn < len) (hnj : nn ≤ j)
    (hpc0 : PwCut (off + nn) c k) : os.WaCut off len (max j (nn + k)) := by
  obtain ⟨hj, hjm⟩ := hj0
  obtain ⟨hpc, hpm⟩ := hpc0
  refine ⟨?_, ?_⟩
  rotate_left
  · rcases Nat.le_total j (nn + k) with h | h
    · rw [Nat.max_eq_right h]; omega
    · rw [Nat.max_eq_left h]; exact hjm
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
  have hcj : os.WaCut off.toNat data.length j := ⟨Or.inl (Or.inl hj0), Or.inl hj0⟩
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
    waCut_step _ _ _ _ _ _ hcj hcn hcdef hk hnl hnj hpc
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
