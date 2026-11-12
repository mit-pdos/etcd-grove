/-
The proof of `Spec/os/File__WriteAt.lean`: one attempt (`PWriteStart`, `PWriteFinish`) per
iteration of the model's loop over chunks of at most 1 GiB, each retried on `EINTR`, by Löb
induction over every iteration, the loop's argument `nn` (the bytes written whole so far) named
first (`wp_call1_gen`); the invariant is the file as a write of the first `j ≥ nn` bytes left it,
and a chunk's attempt of `k` bytes at `off + nn` leaves that of `max j (nn + k)`
(`Proof/os/WriteChunks.lean`).
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

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

private theorem wp_call1_gen (F : val) (n0 : w64) (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n = n0⌝ -∗ WP (App (Val F) (Val #n)) {{ Φ }}) ⊢
    WP (App (Val F) (Val #n0)) {{ Φ }} := by
  iintro H
  iapply H
  ipureintro; rfl

private theorem sintZ_W64 (x : Nat) (h : x < 2 ^ 63) : sint.Z (W64 x) = x := by
  simp only [sint.Z, W64]; rw [BitVec.toInt_ofInt, Int.bmod]; split <;> omega

private theorem sintNat_W64 (x : Nat) (h : x < 2 ^ 63) : sint.nat (W64 x) = x := by
  simp only [sint.nat]; rw [show (W64 x).toInt = x from sintZ_W64 x h]; simp

private theorem W64_add (a b : Nat) : W64 a + W64 b = W64 (a + b : Nat) := by
  show BitVec.ofInt 64 (a : Int) + BitVec.ofInt 64 (b : Int) = BitVec.ofInt 64 ((a + b : Nat) : Int)
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

private theorem W64_sub (a b : Nat) (_ha : a < 2 ^ 63) (h : b ≤ a) :
    W64 a - W64 b = W64 (a - b : Nat) := by
  show BitVec.ofInt 64 (a : Int) - BitVec.ofInt 64 (b : Int) = BitVec.ofInt 64 ((a - b : Nat) : Int)
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

private theorem W64_inj (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    W64 a = W64 b ↔ a = b := by
  constructor
  · intro h; have := congrArg sint.Z h; rw [sintZ_W64 a ha, sintZ_W64 b hb] at this; omega
  · intro h; rw [h]

private theorem toNat_add_W64 (off : w64) (nn : Nat) (h : off.toNat + nn < 2 ^ 63) :
    (off + W64 nn).toNat = off.toNat + nn := by
  rw [BitVec.toNat_add]
  have : (W64 nn).toNat = nn := by
    simp only [W64]; rw [BitVec.toNat_ofInt]; omega
  rw [this]; exact Nat.mod_eq_of_lt (by omega)

set_option maxHeartbeats 1000000 in
theorem os.File.WriteAt.wp_proof : os.File.WriteAt.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d q m xs hwr hoff hn hn63 hxl hq
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
  iapply wp_call1_gen
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
  -- the invariant: the file as a write of the first `j ≥ nn` bytes left it
  have hm0 : m = { m with size := pwSize m.size off.toNat 0, hi := m.hi } := by
    simp [pwSize]
  obtain ⟨j, hj0⟩ : ∃ j : Nat, (0 : Nat) = j := ⟨_, rfl⟩
  have hj : j ≤ data.length := by omega
  have hnj : nn ≤ j := by omega
  have hnl : nn < data.length := by omega
  have hpg : off.toNat % osPageSize = 0 ∧ data.length ≤ osPageSize → nn = 0 := fun _ => hnn0
  have hal : off.toNat % osPageSize = 0 ∧ data.length ≤ osPageSize → j = 0 ∨ j = data.length :=
    fun _ => .inl hj0.symm
  have hys : xs.map Prod.fst = (pwBytes m.size off.toNat data j xs).map Prod.fst := by
    rw [← hj0, pwBytes_zero _ _ _ _ hxl]
  have hh : m.hi ≤ m.hi := Nat.le_refl _
  ihave Hm := (show osMeta (GF := GF) d.path (DFrac.own q) (some m) ⊢
    osMeta d.path (DFrac.own q) (some { m with size := pwSize m.size off.toNat j, hi := m.hi }) by
      rw [← hj0, ← hm0]) $$ Hm
  clear hm0
  obtain ⟨ys, hy⟩ : ∃ ys, ys = xs := ⟨_, rfl⟩
  ihave Hbs := (show osBytes (GF := GF) d.path (min off.toNat m.size) (DFrac.own 1) xs ⊢
    osBytes d.path (min off.toNat m.size) (DFrac.own 1) ys by rw [hy]) $$ Hbs
  replace hys : ys.map Prod.fst = (pwBytes m.size off.toNat data j xs).map Prod.fst := by
    rw [hy]; exact hys
  clear hy
  obtain ⟨h, hhe⟩ : ∃ h, h = m.hi := ⟨_, rfl⟩
  ihave Hm := (show osMeta (GF := GF) d.path (DFrac.own q)
      (some { m with size := pwSize m.size off.toNat j, hi := m.hi }) ⊢
    osMeta d.path (DFrac.own q) (some { m with size := pwSize m.size off.toNat j, hi := h })
      by rw [hhe]) $$ Hm
  replace hh : m.hi ≤ h := by omega
  clear hhe hj0 hnn0
  iloeb as IH generalizing %nw %nn %j %ys %h %hnw' %hj %hnj %hnl %hpg %hal %hys %hh Hm Hbs Hc
    Hosfd Hsl Hfd HΦ
  subst hnw'
  wp_auto
  have hlZ : sint.Z (sl.len - W64 ↑nn) = ↑(data.length - nn) := by
    rw [hsln, W64_sub _ _ (by omega) (by omega), sintZ_W64 _ (by omega)]
  have h30 : sint.Z (W64 1073741824) = 1073741824 := rfl
  obtain ⟨c, hcdef⟩ : ∃ c, c = min (data.length - nn) 1073741824 := ⟨_, rfl⟩
  have hcn : nn + c ≤ data.length := by omega
  wp_join (Q := fun v => iprop(⌜v = #(W64 ↑(nn + c))⌝)) at (if: _ then _ else _) with [] as %Hv
  · by_cases hbig : 1073741824 < data.length - nn
    · rw [decide_eq_true (by rw [hlZ, h30]; omega)]
      wp_auto
      ipureintro
      rw [show (1073741824 : Int) = ((1073741824 : Nat) : Int) from rfl, W64_add]
      congr 3; omega
    · rw [decide_eq_false (by rw [hlZ, h30]; omega)]
      wp_auto
      ipureintro
      rw [hsln]; congr 3; omega
  subst Hv
  wp_auto
  have hsb : 0 ≤ sint.Z (W64 ↑nn) ∧ sint.Z (W64 ↑nn) ≤ sint.Z (W64 ↑(nn + c)) ∧
      sint.Z (W64 ↑(nn + c)) ≤ sint.Z sl.cap := by
    rw [sintZ_W64 _ (by omega), sintZ_W64 _ (by omega)]; omega
  rw [if_pos hsb]
  have hsb2 : 0 ≤ sint.Z (W64 ↑nn) ∧ sint.Z (W64 ↑nn) ≤ sint.Z (W64 ↑(nn + c)) ∧
      sint.Z (W64 ↑(nn + c)) ≤ sint.Z sl.len := by
    rw [sintZ_W64 _ (by omega), sintZ_W64 _ (by omega)]; omega
  icases (ownSlice_slice (W64 ↑nn) (W64 ↑(nn + c)) sl dqs data hsb2).1 $$ Hsl with
    ⟨Hsl1, Hsl2, Hsl3⟩
  wp_apply wp_bytes_to_string _ _ dqs $$ Hsl2 as Hsl2
  ihave Hsl := (ownSlice_slice (W64 ↑nn) (W64 ↑(nn + c)) sl dqs data hsb2).2 $$ [Hsl1 Hsl2 Hsl3]
  · iframe
  generalize hcd0 : subslice (sint.nat (W64 ↑nn)) (sint.nat (W64 ↑(nn + c))) data = cd
  have hcd : cd = (data.drop nn).take c := by
    rw [← hcd0, sintNat_W64 _ (by omega), sintNat_W64 _ (by omega)]
    simp only [subslice, List.drop_take]; congr 1; omega
  have hcdl : cd.length = c := by rw [hcd]; simp; omega
  clear hcd0
  have hocN : (off + W64 ↑nn).toNat = off.toNat + nn := toNat_add_W64 off nn (by omega)
  have hocI : 0 ≤ (off + W64 ↑nn).toInt := by
    have := BitVec.toInt_eq_toNat_cond (off + W64 ↑nn); split at this <;> omega
  generalize hoc : off + W64 ↑nn = oc at hocN hocI ⊢
  -- the bytes and cells the chunk's attempt takes
  have hyl : ys.length = min (off.toNat + data.length) (pwSize m.size off.toNat j) -
      min off.toNat m.size := by
    have := congrArg List.length hys; simp only [List.length_map, pwBytes_length] at this; exact this
  have hsz : m.size ≤ pwSize m.size off.toNat j := by unfold pwSize; split <;> omega
  icases osBytes_split3_range d.path (min off.toNat m.size) (min oc.toNat (pwSize m.size off.toNat j))
      (min (oc.toNat + c) (pwSize m.size off.toNat j)) (DFrac.own 1) ys
      (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min off.toNat m.size)
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))
      (by omega) (by omega) (by omega) (by omega) (by omega) $$ Hbs with ⟨Hbs1, Hbs2, Hbs3⟩
  icases mcellsAny_split m.maps (min off.toNat m.size) (min oc.toNat (pwSize m.size off.toNat j))
    (off.toNat + data.length) (by omega) (by omega) $$ Hc with ⟨Hc1, Hc23⟩
  icases mcellsAny_split m.maps (min oc.toNat (pwSize m.size off.toNat j)) (oc.toNat + cd.length)
    (off.toNat + data.length) (by omega) (by omega) $$ Hc23 with ⟨Hc2, Hc3⟩
  wp_apply wp_osPWriteStart fd oc cd dq d q { m with size := pwSize m.size off.toNat j, hi := h }
    ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
    CoPset.subseteq_top hwr hocI (by
      simp only [List.length_take, List.length_drop]
      omega)
    (fun hr => hq (by simp only at hr; omega)) $$ Hinv Hosfd Hm Hbs2 Hc2 as %t Hosfd Ht
  wp_apply wp_osPWriteFinish t d.path oc.toNat cd q
    { m with size := pwSize m.size off.toNat j, hi := h }
    ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
    CoPset.subseteq_top $$ Hinv Ht as %k %e %hke Hm Hbs2 Hc2
  obtain ⟨hk, hke, hkal⟩ := hke
  have hkc : k ≤ c := by omega
  -- the file as a write of the first `max j (nn + k)` bytes left it
  ihave Hm := (show osMeta (GF := GF) d.path (DFrac.own q)
      (some { pwMeta { m with size := pwSize m.size off.toNat j, hi := h } oc.toNat cd.length with
        size := pwSize (pwSize m.size off.toNat j) oc.toNat k }) ⊢
    osMeta d.path (DFrac.own q)
      (some { m with size := pwSize m.size off.toNat (max j (nn + k)), hi := max h (oc.toNat + c) })
      by rw [hcdl, hocN, pwSize_chunk _ _ _ _ _ hnj]; exact .rfl) $$ Hm
  have hL2 := pwBytes_length (pwSize m.size off.toNat j) oc.toNat cd k
    ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
      (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j)))
  have hend := pwBytes_chunk_end m.size off.toNat data j nn c k ys hkc hcn hyl
  rw [← hocN] at hend
  ihave Hbs := osBytes_app3 d.path (min off.toNat m.size) (min oc.toNat (pwSize m.size off.toNat j))
    (min (oc.toNat + c) (pwSize m.size off.toNat j)) (DFrac.own 1)
    (ys.take (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size))
    (pwBytes (pwSize m.size off.toNat j) oc.toNat cd k
      ((ys.drop (min oc.toNat (pwSize m.size off.toNat j) - min off.toNat m.size)).take
        (min (oc.toNat + c) (pwSize m.size off.toNat j) - min oc.toNat (pwSize m.size off.toNat j))))
    (ys.drop (min (oc.toNat + c) (pwSize m.size off.toNat j) - min off.toNat m.size))
    (by simp only [List.length_take]; omega)
    (by rw [hL2, hcdl]; rcases hend with h1 | h1
        · left; omega
        · right; exact h1) $$ [Hbs1 Hbs2 Hbs3]
  · iframe
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc23 := mcellsAny_merge m.maps (min oc.toNat (pwSize m.size off.toNat j))
    (oc.toNat + cd.length) (off.toNat + data.length) (by omega) (by omega) $$ [Hc2 Hc3]
  · iframe
  ihave Hc := mcellsAny_merge m.maps (min off.toNat m.size)
    (min oc.toNat (pwSize m.size off.toNat j)) (off.toNat + data.length) (by omega) (by omega)
    $$ [Hc1 Hc23]
  · iframe
  have hys' := pwBytes_chunk m.size off.toNat data cd j nn c k xs ys hnj hj hcn hkc hcd hys
  rw [← hocN] at hys'
  have hJ : max j (nn + k) ≤ data.length := by omega
  have hnJ : nn ≤ max j (nn + k) := by omega
  have hP : osPageSize = 4096 := rfl
  have hal' : off.toNat % osPageSize = 0 ∧ data.length ≤ osPageSize →
      max j (nn + k) = 0 ∨ max j (nn + k) = data.length := fun hc' => by
    have h0 := hpg hc'
    have hcc : c = data.length := by rw [hP] at hc'; omega
    have hk2 := hkal ⟨by rw [hocN, h0, Nat.add_zero]; exact hc'.1, by rw [hcdl, hP]; omega⟩
    rcases hal hc' with h1 | h1 <;> rcases hk2 with h2 | h2 <;> omega
  have hh' : m.hi ≤ max h (oc.toNat + c) := by omega
  clear hend hL2 hyl hsz hxl hlZ hsb hsb2 hys hcd hq hkal hal hh hocI hslz Hlen Hwf
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %(W64 ↑nn) %nn %(max j (nn + k)) %_ %(max h (oc.toNat + c)) %rfl %hJ %hnJ %hnl
      %hpg %hal' %hys' %hh' Hm Hbs Hc Hosfd Hsl Hfd HΦ
  · rw [decide_eq_false he4]
    wp_auto
    rcases hke with ⟨hkc', rfl⟩ | he0
    · rw [hcdl] at hkc'
      by_cases hfull : nn + c = data.length
      · rw [decide_eq_true (show W64 ↑nn + W64 ↑k = sl.len by
          rw [W64_add, hsln]; congr 2; omega)]
        wp_auto
        ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro; exact ⟨hJ, hys', hh', hal', .inl ⟨by omega, hsln, rfl⟩⟩
      · rw [decide_eq_false (show ¬ W64 ↑nn + W64 ↑k = sl.len by
          rw [W64_add, hsln, W64_inj _ _ (by omega) (by omega)]; omega)]
        wp_pure
        wp_pure
        wp_pure
        wp_pure
        wp_pure
        wp_pure
        wp_pure
        have hnw2 : W64 ↑nn + W64 ↑k = W64 ↑(nn + k) := W64_add nn k
        have hnJ2 : nn + k ≤ max j (nn + k) := by omega
        have hnl2 : nn + k < data.length := by omega
        have hpg2 : off.toNat % osPageSize = 0 ∧ data.length ≤ osPageSize → nn + k = 0 :=
          fun hc' => by have := hpg hc'; rw [hP] at hc'; omega
        iapply IH $$ %(W64 ↑nn + W64 ↑k) %(nn + k) %(max j (nn + k)) %_ %(max h (oc.toNat + c))
          %hnw2 %hJ %hnJ2 %hnl2 %hpg2 %hal' %hys' %hh' Hm Hbs Hc Hosfd Hsl Hfd HΦ
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
          exact ⟨hJ, hys', hh', hal', .inr ⟨rfl, by intro h; cases h⟩⟩
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
          exact ⟨hJ, hys', hh', hal', .inr ⟨rfl, by intro h; cases h⟩⟩

end proof

end EtcdGrove
end Perennial
