/-
The proof of `Spec/os/File__ReadAt.lean`: the model's loop, by Löb induction over every iteration
(a successful `pread` reads a non-empty prefix of what is left, so the loop goes on until `b` is
full), the bytes split at what has been read. The racing read (`wp_proofRacy`): by Löb induction over every iteration,
the arguments named first (`wp_call3_gen`); the invariant splits the slice at `n`, the bytes read
so far (exact at every held byte) and the rest of `b` (anything).
-/
module

public import Proof.os.ForLoeb
public import Proof.os.ErrorOk
public import Spec.os.File__ReadAt
public import Proof.os.ReadAtOwn
public import Proof.os.CrashFile
public import GooseLang.Ext.Fs.NoErrSpecsOpen

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

private theorem w64_sintZ (x : w64) (h : x.toNat < 2 ^ 63) : sint.Z x = x.toNat := by
  have := BitVec.toInt_eq_toNat_cond x; simp only [sint.Z]; split at this <;> omega

private theorem w64_sintNat (x : w64) (h : x.toNat < 2 ^ 63) : sint.nat x = x.toNat := by
  simp only [sint.nat]; rw [show x.toInt = x.toNat from w64_sintZ x h]; simp

private theorem w64_toNat_of_sintZ (x : w64) (h : 0 ≤ sint.Z x) : x.toNat < 2 ^ 63 := by
  have := BitVec.toInt_eq_toNat_cond x; simp only [sint.Z] at h; split at this <;> omega

private theorem w64_add_toNat (a b : w64) (h : a.toNat + b.toNat < 2 ^ 63) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)

/-- Name the arguments of a call of three arguments, to generalize over them. -/
private theorem wp_call3_gen (F : val) (b0 : GoSlice) (o0 n0 : w64) (Φ : val → IProp GF) :
    (∀ (b : GoSlice) (o n : w64), ⌜b = b0 ∧ o = o0 ∧ n = n0⌝ -∗
      WP (App (App (App (Val F) (Val #b)) (Val #o)) (Val #n)) {{ Φ }}) ⊢
    WP (App (App (App (Val F) (Val #b0)) (Val #o0)) (Val #n0)) {{ Φ }} := by
  iintro H
  iapply H
  ipureintro; exact ⟨rfl, rfl, rfl⟩

set_option hygiene false in
/-- `ReadAt`'s loop after an iteration's `pread`, its result `hre` over the bytes left. -/
local macro "readat_tail" : tactic => `(tactic| (
    obtain ⟨k, hkl, rfl, hke0⟩ := hre
    have hdrop : (xs.drop n.toNat).length = cur.length := by rw [List.length_drop, hcl]; omega
    wp_apply wp_string_to_bytes (((xs.drop n.toNat).map Prod.fst).take k) as %tmp ⟨Htmp, -⟩
    by_cases hk0 : k = 0
    · subst hk0
      have he0 : e ≠ 0 := by
        intro h; rcases hke0 h with h' | h'
        · omega
        · rw [h'] at hdrop; simp at hdrop; omega
      icases ownSlice_len tmp _ _ $$ Htmp with %Htl
      have htl0 : tmp.len = W64 0 := by
        apply BitVec.eq_of_toInt_eq
        simp only [List.take_zero] at Htl; simp only [sint.nat, sint.Z] at Htl
        rw [show (W64 0).toInt = 0 from rfl]; simp at Htl; omega
      wp_apply wp_slice_copy_of_len_zero b tmp htl0
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        iapply IH $$ %b %o %n %pre %cur %hk %hb' %ho' %hpre %hcl Hpre Hcur Hosfd Hm Hbs1 Hbs2 Hfd HΦ
      · rw [decide_eq_false he4]
        try wp_auto
        have he0' : ¬ e = W64 0 := he0
        simp only [decide_eq_false he0', Bool.not_false]
        try wp_auto
        wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn as %pe #Hok
        ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
        ihave Hsl := hcomb cur $$ [Hpre Hcur]
        · iframe
        ihave Hbs := hbsj $$ [Hbs1 Hbs2]
        · iframe
        iapply HΦ
        iframe Hokn
        iframe
        isplitl []
        · isplitl [] <;> (try isplitl []) <;> iassumption
        ipureintro
        exact ⟨by simp [hpl, hcl]; omega, .inr (by intro h; cases h)⟩
    · have hrl : (((xs.drop n.toNat).map Prod.fst).take k).length = k := by simp; omega
      wp_apply wp_slice_copy b cur tmp _ (DFrac.own 1) $$ [Hcur Htmp] as %mm ⟨%hmm, Hcur, -⟩
      · iframe
      have hmmN : mm.toNat = k := by
        rw [← w64_sintNat mm (by
          have : sint.nat mm = k := by rw [hmm, hrl]; omega
          have := BitVec.toInt_eq_toNat_cond mm; simp only [sint.nat] at *; split at this <;> omega)]
        rw [hmm, hrl]; omega
      have hmmZ : sint.Z mm = k := by rw [w64_sintZ _ (by omega), hmmN]
      have hc2l : ((((xs.drop n.toNat).map Prod.fst).take k).take cur.length ++
          cur.drop (((xs.drop n.toNat).map Prod.fst).take k).length).length = cur.length := by
        simp; omega
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        iapply IH $$ %b %o %n %pre %_ %hk %hb' %ho' %hpre %(hc2l.trans hcl) Hpre Hcur Hosfd Hm Hbs1
          Hbs2 Hfd HΦ
      · rw [decide_eq_false he4]
        try wp_auto
        by_cases he0 : e = W64 0
        · subst he0
          have hm0 : mm ≠ W64 0 := by
            intro h; rw [h, show sint.Z (W64 0) = 0 from rfl] at hmmZ; omega
          try wp_auto
          rw [decide_eq_false hm0]
          try wp_auto
          have hmmNat : sint.nat mm = k := by rw [hmm, hrl]; omega
          rw [if_pos ⟨by omega, by omega, Hbwf.2⟩]
          icases (ownSlice_split_all mm b (DFrac.own 1) _ ⟨by omega, by omega⟩).1 $$ Hcur
            with ⟨Hc1, Hc2⟩
          have hnZ : sint.Z n = n.toNat := w64_sintZ n hnN
          have hnmN : (n + mm).toNat = n.toNat + k := by rw [w64_add_toNat _ _ (by omega), hmmN]
          have hnmZ : sint.Z (n + mm) = n.toNat + k := by
            rw [w64_sintZ _ (by omega), hnmN]; omega
          ihave Hc1 := (show slice.slice b w8 (W64 0) mm ↦*
                ((((xs.drop n.toNat).map Prod.fst).take k).take cur.length ++
                  cur.drop (((xs.drop n.toNat).map Prod.fst).take k).length).take (sint.nat mm) ⊢
              slice.slice sl w8 n (n + mm) ↦*
                ((((xs.drop n.toNat).map Prod.fst).take k).take cur.length ++
                  cur.drop (((xs.drop n.toNat).map Prod.fst).take k).length).take (sint.nat mm) by
            rw [hb', slice_slice sl n sl.len (W64 0) mm ⟨by omega, by omega⟩,
              show n + W64 0 = n from BitVec.add_zero n]) $$ Hc1
          ihave Hpre := (ownSlice_combine n sl (DFrac.own 1) pre _ (W64 0) (n + mm)
            ⟨by rw [w64_sintNat n hnN, hpl, hzn0]; rfl, by decide, by rw [hnZ, hz0]; omega,
              by rw [hnZ, hnmZ]; omega⟩) $$ Hpre Hc1
          have hb'' : slice.slice b w8 mm b.len = slice.slice sl w8 (n + mm) sl.len := by
            rw [hb', slice_slice sl n sl.len mm _ ⟨by omega, by omega⟩]
            congr 1
            show n + (sl.len - n) = sl.len
            rw [BitVec.add_comm, BitVec.sub_add_cancel]
          have ho'' : o + mm = off + (n + mm) := by rw [ho', BitVec.add_assoc]
          have hk' : (n + mm).toNat ≤ vs.length := by omega
          have hpre' : pre ++ ((((xs.drop n.toNat).map Prod.fst).take k).take cur.length ++
              cur.drop (((xs.drop n.toNat).map Prod.fst).take k).length).take (sint.nat mm) =
              (xs.map Prod.fst).take (n + mm).toNat := by
            have hA : (((xs.drop n.toNat).map Prod.fst).take k).take cur.length =
                ((xs.drop n.toNat).map Prod.fst).take k := List.take_of_length_le (by simp; omega)
            rw [hmmNat, hnmN, hpre, hA, List.take_append_of_le_length (by simp; omega)]
            simp only [List.take_take, Nat.min_self, List.take_add, List.map_drop]
          have hcl' : (((((xs.drop n.toNat).map Prod.fst).take k).take cur.length ++
              cur.drop (((xs.drop n.toNat).map Prod.fst).take k).length).drop (sint.nat mm)).length =
              vs.length - (n + mm).toNat := by
            rw [hmmNat, hnmN]; simp; omega
          -- the bytes, split at the new count
          ihave ⟨Hbs1, Hbs2⟩ := (show osBytes (GF := GF) d.ino off.toNat dqb (xs.take n.toNat) ∗
              osBytes d.ino (off.toNat + n.toNat) dqb (xs.drop n.toNat) ⊢
              osBytes d.ino off.toNat dqb (xs.take (n + mm).toNat) ∗
              osBytes d.ino (off.toNat + (n + mm).toNat) dqb (xs.drop (n + mm).toNat) by
            refine hbsj.trans ?_
            conv => lhs; rw [← List.take_append_drop (n + mm).toNat xs]
            unfold osBytes
            refine (bytesG_append _ _ _ _ _ _).1.trans ?_
            rw [List.length_take, Nat.min_eq_left (by omega)]) $$ [Hbs1 Hbs2]
          · iframe
          try wp_auto
          rw [show b.len - mm = (slice.slice b w8 mm b.len).len from rfl]
          iapply IH $$ %(slice.slice b w8 mm b.len) %(o + mm) %(n + mm) %_ %_ %hk' %hb'' %ho''
            %hpre' %hcl' Hpre Hc2 Hosfd Hm Hbs1 Hbs2 Hfd HΦ
        · have he0' : ¬ e = W64 0 := he0
          simp only [decide_eq_false he0', Bool.not_false]
          try wp_auto
          wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn as %pe #Hok
          ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
          ihave Hsl := hcomb _ $$ [Hpre Hcur]
          · iframe
          ihave Hbs := hbsj $$ [Hbs1 Hbs2]
          · iframe
          iapply HΦ
          iframe Hokn
          iframe
          isplitl []
          · isplitl [] <;> (try isplitl []) <;> iassumption
          ipureintro
          refine ⟨?_, .inr (by intro h; cases h)⟩
          rw [List.length_append, hpl, hc2l, hcl]; omega
  ))

-- (two copies of the loop's tail, `readat_tail`: one per `pread` count)
set_option maxHeartbeats 600000 in
theorem os.File.ReadAt.wp_proof_long : os.File.ReadAt.specLong (GF := GF) (hG := hG) := by
  intro f fd name dqf sl vs off dq dqm dqb d m xs hrd hoff hend hin hxl
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb⟩, Hsl, Hosfd, Hm, Hbs⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl _ vs $$ Hsl with %Hlen
  try wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_pure
  wp_pure
  wp_load
  wp_pure
  wp_pure
  wp_pure
  iapply wp_call3_gen
  iintro %b %o %n %hbon
  obtain ⟨hb, ho, hn⟩ := hbon
  icases ownSlice_wf sl _ vs $$ Hsl with %Hwf
  have hslz : sint.Z sl.len = vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  clear Hlen
  icases (ownSlice_split_all (W64 0) sl (DFrac.own 1) vs
    ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩).1 $$ Hsl with ⟨Hpre, Hcur⟩
  obtain ⟨pre, hpre0⟩ : ∃ pre : List w8, pre = [] := ⟨_, rfl⟩
  obtain ⟨cur, hcur0⟩ : ∃ cur : List w8, cur = vs := ⟨_, rfl⟩
  ihave Hpre := (show slice.slice sl w8 (W64 0) (W64 0) ↦* vs.take (sint.nat (W64 0)) ⊢
    slice.slice sl w8 (W64 0) n ↦* pre by
      rw [hn, hpre0, show sint.nat (W64 0) = 0 from rfl, List.take_zero]) $$ Hpre
  ihave Hcur := (show slice.slice sl w8 (W64 0) sl.len ↦* vs.drop (sint.nat (W64 0)) ⊢
    b ↦* cur by
      rw [hb, hcur0, show sint.nat (W64 0) = 0 from rfl, List.drop_zero, ← slice_slice_trivial]) $$ Hcur
  -- the bytes, split at what has been read
  ihave ⟨Hbs1, Hbs2⟩ := (show osBytes (GF := GF) d.ino off.toNat dqb xs ⊢
      osBytes d.ino off.toNat dqb (xs.take n.toNat) ∗
      osBytes d.ino (off.toNat + n.toNat) dqb (xs.drop n.toNat) by
    rw [hn, show (W64 0).toNat = 0 from rfl, List.take_zero, List.drop_zero, Nat.add_zero]
    unfold osBytes
    iintro H; isplitr
    · unfold bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
    · iexact H) $$ Hbs
  have hk : n.toNat ≤ vs.length := by rw [hn]; simp
  have hb' : b = slice.slice sl w8 n sl.len := by rw [hb, hn]; exact slice_slice_trivial sl
  have ho' : o = off + n := by rw [ho, hn]; exact (BitVec.add_zero off).symm
  have hpre : pre = (xs.map Prod.fst).take n.toNat := by rw [hpre0, hn]; rfl
  have hcl : cur.length = vs.length - n.toNat := by rw [hcur0, hn]; simp
  clear hb ho hn hpre0 hcur0
  have hoffN : off.toNat < 2 ^ 63 := by
    have := BitVec.toInt_eq_toNat_cond off; split at this <;> omega
  try wp_auto
  iloeb as IH generalizing %b %o %n %pre %cur %hk %hb' %ho' %hpre %hcl Hpre Hcur Hosfd Hm Hbs1 Hbs2
    Hfd HΦ
  have hnN : n.toNat < 2 ^ 63 := by omega
  have hoN : o.toNat = off.toNat + n.toNat := by rw [ho']; exact w64_add_toNat _ _ (by omega)
  have hoI : 0 ≤ o.toInt := by
    have := BitVec.toInt_eq_toNat_cond o; split at this <;> omega
  have hpl : pre.length = n.toNat := by rw [hpre]; simp [hxl]; omega
  icases ownSlice_len b _ cur $$ Hcur with %Hblen
  icases ownSlice_wf b _ cur $$ Hcur with %Hbwf
  have hblN : b.len.toNat = cur.length := by
    have h := w64_toNat_of_sintZ _ Hblen.2; rw [Hblen.1, w64_sintNat _ h]
  have hblZ : sint.Z b.len = cur.length := by rw [w64_sintZ _ (by omega), hblN]
  have hz0 : sint.Z (W64 0) = 0 := rfl
  have hzn0 : sint.nat (W64 0) = 0 := rfl
  have hcomb : ∀ cur' : List w8,
      (slice.slice sl w8 (W64 0) n ↦* pre ∗ b ↦* cur' : IProp GF) ⊢ sl ↦* (pre ++ cur') := by
    intro cur'
    refine BIBase.Entails.trans ?_ (ownSlice_trivial_slice sl _ _).2
    rw [hb']
    iintro ⟨H1, H2⟩
    iapply (ownSlice_combine n sl (DFrac.own 1) pre cur' (W64 0) sl.len
      ⟨by rw [w64_sintNat n hnN, hpl, hzn0]; rfl, by decide, by rw [w64_sintZ n hnN, hz0]; omega,
        by rw [w64_sintZ n hnN]; omega⟩) $$ H1 H2
  have hbsj : (osBytes (GF := GF) d.ino off.toNat dqb (xs.take n.toNat) ∗
      osBytes d.ino (off.toNat + n.toNat) dqb (xs.drop n.toNat)) ⊢ osBytes d.ino off.toNat dqb xs := by
    conv => rhs; rw [← List.take_append_drop n.toNat xs]
    unfold osBytes
    refine BIBase.Entails.trans ?_ (bytesG_append _ _ _ _ _ _).2
    rw [List.length_take, Nat.min_eq_left (by omega)]
  by_cases hl0 : b.len = W64 0
  · rw [decide_eq_true hl0]
    try wp_auto
    have hc0 : cur.length = 0 := by rw [← hblN, hl0]; rfl
    ihave Hsl := hcomb cur $$ [Hpre Hcur]
    · iframe
    ihave Hbs := hbsj $$ [Hbs1 Hbs2]
    · iframe
    ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
    iapply HΦ
    iframe Hokn
    iframe
    isplitl []
    · isplitl [] <;> (try isplitl []) <;> iassumption
    ipureintro
    have hnl : n.toNat = vs.length := by omega
    have hc' : cur = [] := List.length_eq_zero_iff.1 hc0
    refine ⟨by simp [hpl, hc0]; omega, .inl ⟨?_, rfl, ?_⟩⟩
    · apply BitVec.eq_of_toNat_eq; rw [hnl]; simp only [W64]; rw [BitVec.toNat_ofInt]; omega
    · rw [hc', List.append_nil, hpre, hnl]; exact List.take_of_length_le (by simp [hxl])
  · rw [decide_eq_false hl0]
    try wp_auto
    have hcpos : 0 < cur.length := by
      apply Nat.pos_of_ne_zero; intro h0; apply hl0
      apply BitVec.eq_of_toNat_eq; rw [hblN, h0]; rfl
    by_cases hmx : sint.Z (W64 1073741824) < sint.Z b.len
    · -- a buffer past `maxRW`: one `pread` of its first `maxRW` bytes
      rw [decide_eq_true hmx]
      try wp_auto
      have hcbig : 1073741824 < cur.length := by
        rw [hblZ, show sint.Z (W64 1073741824) = 1073741824 from rfl] at hmx; omega
      have hdl : ((xs.drop n.toNat).take 1073741824).length =
          min (W64 1073741824).toNat (m.size - o.toNat) := by
        rw [List.length_take, List.length_drop, show (W64 1073741824).toNat = 1073741824 from rfl, hoN]
        omega
      ihave ⟨Hbsa, Hbsb⟩ := (show osBytes (GF := GF) d.ino (off.toNat + n.toNat) dqb (xs.drop n.toNat) ⊢
          osBytes d.ino o.toNat dqb ((xs.drop n.toNat).take 1073741824) ∗
          osBytes d.ino (o.toNat + ((xs.drop n.toNat).take 1073741824).length) dqb
            ((xs.drop n.toNat).drop 1073741824) by
        rw [hoN]
        conv => lhs; rw [← List.take_append_drop 1073741824 (xs.drop n.toNat)]
        unfold osBytes; exact (bytesG_append _ _ _ _ _ _).1) $$ Hbs2
      try wp_auto
      wp_stub os.fsPRead.impl
      wp_apply wp_osPRead fd o (W64 1073741824) dq dqm dqb d m ((xs.drop n.toNat).take 1073741824)
        CoPset.subseteq_top hrd hoI hdl $$ Hinv Hosfd Hm Hbsa as %r %e %hre0 Hosfd Hm Hbsa
      ihave Hbs2 := (show osBytes (GF := GF) d.ino o.toNat dqb ((xs.drop n.toNat).take 1073741824) ∗
          osBytes d.ino (o.toNat + ((xs.drop n.toNat).take 1073741824).length) dqb
            ((xs.drop n.toNat).drop 1073741824) ⊢
          osBytes d.ino (off.toNat + n.toNat) dqb (xs.drop n.toNat) by
        rw [hoN]
        conv => rhs; rw [← List.take_append_drop 1073741824 (xs.drop n.toNat)]
        unfold osBytes; exact (bytesG_append _ _ _ _ _ _).2) $$ [Hbsa Hbsb]
      · iframe
      have hre : ∃ k ≤ (xs.drop n.toNat).length, r = ((xs.drop n.toNat).map Prod.fst).take k ∧
          (e = 0 → 0 < k ∨ xs.drop n.toNat = []) := by
        obtain ⟨k, hkl, hr, hke⟩ := hre0
        simp only [List.length_take, List.length_drop] at hkl
        refine ⟨k, by simp only [List.length_drop]; omega, ?_, ?_⟩
        · rw [hr]; simp only [List.map_take, List.take_take]; congr 1; omega
        · intro he; rcases hke he with h | h
          · exact .inl h
          · exfalso
            have h' := congrArg List.length h
            simp only [List.length_take, List.length_drop, List.length_nil] at h'
            omega
      readat_tail
    · rw [decide_eq_false hmx]
      try wp_auto
      have hdl : (xs.drop n.toNat).length = min b.len.toNat (m.size - o.toNat) := by
        rw [List.length_drop, hblN, hcl, hoN]; omega
      ihave Hbs2 := (show osBytes (GF := GF) d.ino (off.toNat + n.toNat) dqb (xs.drop n.toNat) ⊢
        osBytes d.ino o.toNat dqb (xs.drop n.toNat) by rw [hoN]) $$ Hbs2
      try wp_auto
      wp_stub os.fsPRead.impl
      wp_apply wp_osPRead fd o b.len dq dqm dqb d m (xs.drop n.toNat) CoPset.subseteq_top hrd hoI hdl
        $$ Hinv Hosfd Hm Hbs2 as %r %e %hre Hosfd Hm Hbs2
      ihave Hbs2 := (show osBytes (GF := GF) d.ino o.toNat dqb (xs.drop n.toNat) ⊢
        osBytes d.ino (off.toNat + n.toNat) dqb (xs.drop n.toNat) by rw [hoN]) $$ Hbs2
      readat_tail

theorem os.File.ReadAt.wp_proof : os.File.ReadAt.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf sl vs off dq dqm dqb d m xs hrd hoff _ hend hin hxl
  exact os.File.ReadAt.wp_proof_long f fd name dqf sl vs off dq dqm dqb d m xs hrd hoff hend hin hxl

/-- A `pread` exact at every byte of the ranges `rs'` it saw is exact at every byte `rs` says, if
`rs'` says at least as much. -/
private theorem held_read_of (rs rs' : List (Nat × DFrac × List ByteG)) (o n : w64) (r : List w8)
    (hsub : ∀ i b, os.heldByte rs i b → os.heldByte rs' i b)
    (h1 : ∀ x ∈ rs', ∀ k (hk : k < x.2.2.length), o.toNat ≤ x.1 + k →
      x.1 + k < o.toNat + n.toNat →
      ∀ (h : x.1 + k - o.toNat < r.length), r[x.1 + k - o.toNat] = x.2.2[k].1) :
    ∀ i b, os.heldByte rs i b → o.toNat ≤ i → i < o.toNat + n.toNat →
      i - o.toNat < r.length → r[i - o.toNat]? = some b := by
  intro i b hh hi1 hi2 hlt
  obtain ⟨x, hx, hx1, hxb⟩ := hsub i b hh
  have hk : i - x.1 < x.2.2.length := by
    apply Classical.byContradiction; intro hk
    rw [List.getElem?_eq_none (by omega)] at hxb; cases hxb
  have hidx : x.1 + (i - x.1) - o.toNat = i - o.toNat := by omega
  rw [← hidx, List.getElem?_eq_getElem (by omega),
    h1 x hx (i - x.1) hk (by omega) (by omega) (by omega)]
  rw [List.getElem?_eq_getElem hk] at hxb
  simpa using hxb

/-- An empty `pread` that reached no byte of the ranges `rs'` reached none that `rs` says, if `rs'`
says at least as much. -/
private theorem held_empty_of (rs rs' : List (Nat × DFrac × List ByteG)) (o n : w64)
    (hsub : ∀ i b, os.heldByte rs i b → os.heldByte rs' i b)
    (h2 : ∀ x ∈ rs', ∀ k (_ : k < x.2.2.length), o.toNat ≤ x.1 + k →
      x.1 + k < o.toNat + n.toNat → False) :
    ∀ i b, os.heldByte rs i b → o.toNat ≤ i → i < o.toNat + n.toNat → False := by
  intro i b hh hi1 hi2
  obtain ⟨x, hx, hx1, hxb⟩ := hsub i b hh
  have hk : i - x.1 < x.2.2.length := by
    apply Classical.byContradiction; intro hk
    rw [List.getElem?_eq_none (by omega)] at hxb; cases hxb
  exact h2 x hx (i - x.1) hk (by omega) (by omega)

/-- **The racing read, generic in its `pread`s' errnos** (`specRacyLt` with a `*PathError` only
of an errno `e ≠ 0` with `Pe e`): over a semantics whose `pread` steps return an errno with `Pe`
(`hpost`, a strengthening of their weakest preconditions as `wp_ext_post` gives). `specRacyLt`
(at `Pe e := FsNoErr → e = 0`) is its instance. -/
theorem os.File.ReadAt.wp_proofRacyLtQ (Pe : w64 → Prop)
    (hpost : ∀ (fd o n : w64) (Φ : val → IProp GF),
      WP (ExternalOp fsExt.name "PRead" (Val (PairV (#fd) (PairV (#o) (#n)))))
          {{ r, ⌜∀ r0 (e : w64), r = PairV r0 (#e) → Pe e⌝ -∗ Φ r }} ⊢
        WP (ExternalOp fsExt.name "PRead" (Val (PairV (#fd) (PairV (#o) (#n))))) {{ Φ }})
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (vs : List w8)
    (off : w64) (dq : DFrac) (d : OsFd) (rs : List (Nat × DFrac × List ByteG)) (P : IProp GF)
    (E : CoPset) (eof : GoInterface)
    (hrd : d.readable = true) (hoff : 0 ≤ off.toInt) (hn2 : vs.length ≤ 0x40000000)
    (hend : off.toNat + vs.length < 2 ^ 63) (hE : ↑osN ⊆ E) :
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦* vs ∗
      osFd (GF := GF) fd dq d ∗ P ∗ os.heldAcc d.ino rs P E ∗
      globalAddr io.EOF ↦□ eof }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"ReadAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ osFd fd dq d ∗ P ∗
      ∃ vs' : List w8, sl ↦* vs' ∗
        ⌜vs'.length = vs.length ∧ n.toNat ≤ vs.length ∧
          (∀ i b, os.heldByte rs i b → off.toNat ≤ i → i < off.toNat + n.toNat →
            vs'[i - off.toNat]? = some b)⌝ ∗
        (⌜(err = interface.nil ∧ n.toNat = vs.length) ∨
           (err = eof ∧ n.toNat < vs.length ∧ ∀ i b, os.heldByte rs i b → off.toNat ≤ i →
              i < off.toNat + vs.length → i < off.toNat + n.toNat)⌝ ∨
         (∃ pe : Loc, ⌜err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe ∧
           ∃ e : w64, Pe e ∧ e ≠ W64 0⌝ ∗ fmtErrorOk err)) }} := by
  -- one `pread`, atomic: the accessor opened around it (`wp_atomic`, at `E`), the facts of the
  -- bytes it opened to restated over `rs`
  have hread : ∀ (o n : w64) (Φ : val → IProp GF), 0 ≤ o.toInt →
      ⊢ osInv (GF := GF) -∗ os.heldAcc d.ino rs P E -∗ osFd (GF := GF) fd dq d -∗ P -∗
        (∀ r : List w8, ∀ e : w64,
          ⌜∀ i b, os.heldByte rs i b → o.toNat ≤ i → i < o.toNat + n.toNat →
            i - o.toNat < r.length → r[i - o.toNat]? = some b⌝ -∗
          ⌜e = W64 0 → r = [] → ∀ i b, os.heldByte rs i b → o.toNat ≤ i →
            i < o.toNat + n.toNat → False⌝ -∗ ⌜Pe e⌝ -∗
          osFd (GF := GF) fd dq d -∗ P -∗ Φ (PairV (#r) (#e))) -∗
        WP (ExternalOp fsExt.name "PRead" (Val (PairV (#fd) (PairV (#o) (#n))))) {{ Φ }} := by
    intro o n Φ hoI
    unfold os.heldAcc
    iintro #Hinv #Hacc Hfd HP HΦ
    iapply hpost
    iapply (wp_atomic (E2 := E))
    imod Hacc $$ HP with ⟨%rs', Hbs, %hsub, Hcl⟩
    imodintro
    iapply wp_osPRead_racy_list fd o n dq d rs' hE hrd hoI _ $$ Hinv Hfd Hbs
    iintro %r %e %h1 %h2 Hfd Hbs
    imod Hcl $$ Hbs with HP
    imodintro
    iintro %hP
    iapply HΦ $$ %r %e %(held_read_of rs rs' o n r hsub h1)
      %(fun he hr => held_empty_of rs rs' o n hsub (h2 he hr)) %(hP _ _ rfl) Hfd HP
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb⟩, Hsl, Hosfd, Hbs, #Hacc, #Heof⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl _ vs $$ Hsl with %Hlen
  try wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_pure
  wp_pure
  wp_load
  wp_pure
  wp_pure
  wp_pure
  iapply wp_call3_gen
  iintro %b %o %n %hbon
  obtain ⟨hb, ho, hn⟩ := hbon
  icases ownSlice_wf sl _ vs $$ Hsl with %Hwf
  have hslz : sint.Z sl.len = vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  clear Hlen
  icases (ownSlice_split_all (W64 0) sl (DFrac.own 1) vs
    ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩).1 $$ Hsl with ⟨Hpre, Hcur⟩
  obtain ⟨pre, hpre0⟩ : ∃ pre : List w8, pre = [] := ⟨_, rfl⟩
  obtain ⟨cur, hcur0⟩ : ∃ cur : List w8, cur = vs := ⟨_, rfl⟩
  ihave Hpre := (show slice.slice sl w8 (W64 0) (W64 0) ↦* vs.take (sint.nat (W64 0)) ⊢
    slice.slice sl w8 (W64 0) n ↦* pre by
      rw [hn, hpre0, show sint.nat (W64 0) = 0 from rfl, List.take_zero]) $$ Hpre
  ihave Hcur := (show slice.slice sl w8 (W64 0) sl.len ↦* vs.drop (sint.nat (W64 0)) ⊢
    b ↦* cur by
      rw [hb, hcur0, show sint.nat (W64 0) = 0 from rfl, List.drop_zero, ← slice_slice_trivial]) $$ Hcur
  have hk : n.toNat ≤ vs.length := by rw [hn]; simp
  have hb' : b = slice.slice sl w8 n sl.len := by rw [hb, hn]; exact slice_slice_trivial sl
  have ho' : o = off + n := by rw [ho, hn]; exact (BitVec.add_zero off).symm
  have hpl : pre.length = n.toNat := by rw [hpre0, hn]; rfl
  have hcl : cur.length = vs.length - n.toNat := by rw [hcur0, hn]; simp
  have hpv : ∀ i bt, os.heldByte rs i bt → off.toNat ≤ i → i < off.toNat + n.toNat →
      pre[i - off.toNat]? = some bt := by
    intro i bt _ h1 h2; rw [hn] at h2; simp at h2; omega
  clear hb ho hn hpre0 hcur0
  have hoffN : off.toNat < 2 ^ 63 := by
    have := BitVec.toInt_eq_toNat_cond off; split at this <;> omega
  try wp_auto
  iloeb as IH generalizing %b %o %n %pre %cur %hk %hb' %ho' %hpl %hcl %hpv Hpre Hcur Hosfd Hbs Hfd HΦ
  have hnN : n.toNat < 2 ^ 63 := by omega
  have hoN : o.toNat = off.toNat + n.toNat := by rw [ho']; exact w64_add_toNat _ _ (by omega)
  have hoI : 0 ≤ o.toInt := by
    have := BitVec.toInt_eq_toNat_cond o; split at this <;> omega
  icases ownSlice_len b _ cur $$ Hcur with %Hblen
  icases ownSlice_wf b _ cur $$ Hcur with %Hbwf
  have hblN : b.len.toNat = cur.length := by
    have h := w64_toNat_of_sintZ _ Hblen.2; rw [Hblen.1, w64_sintNat _ h]
  have hblZ : sint.Z b.len = cur.length := by rw [w64_sintZ _ (by omega), hblN]
  have hz0 : sint.Z (W64 0) = 0 := rfl
  have hzn0 : sint.nat (W64 0) = 0 := rfl
  have hcomb : ∀ cur' : List w8,
      (slice.slice sl w8 (W64 0) n ↦* pre ∗ b ↦* cur' : IProp GF) ⊢ sl ↦* (pre ++ cur') := by
    intro cur'
    refine BIBase.Entails.trans ?_ (ownSlice_trivial_slice sl _ _).2
    rw [hb']
    iintro ⟨H1, H2⟩
    iapply (ownSlice_combine n sl (DFrac.own 1) pre cur' (W64 0) sl.len
      ⟨by rw [w64_sintNat n hnN, hpl, hzn0]; rfl, by decide, by rw [w64_sintZ n hnN, hz0]; omega,
        by rw [w64_sintZ n hnN]; omega⟩) $$ H1 H2
  have hfin : ∀ cur' : List w8, cur'.length = cur.length →
      (cur'.length + pre.length = vs.length ∧ (pre ++ cur').length = vs.length) ∧
      ∀ i bt, os.heldByte rs i bt → off.toNat ≤ i → i < off.toNat + n.toNat →
        (pre ++ cur')[i - off.toNat]? = some bt := by
    intro cur' hc'
    refine ⟨⟨by omega, by simp; omega⟩, fun i bt hh h1 h2 => ?_⟩
    rw [List.getElem?_append_left (by omega)]; exact hpv i bt hh h1 h2
  by_cases hl0 : b.len = W64 0
  · rw [decide_eq_true hl0]
    try wp_auto
    have hc0 : cur.length = 0 := by rw [← hblN, hl0]; rfl
    ihave Hsl := hcomb cur $$ [Hpre Hcur]
    · iframe
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> (try isplitl []) <;> iassumption
    obtain ⟨⟨-, hl⟩, hx⟩ := hfin cur rfl
    isplitr
    · ipureintro; exact ⟨hl, by omega, hx⟩
    ileft; ipureintro; exact .inl ⟨rfl, by omega⟩
  · rw [decide_eq_false hl0]
    try wp_auto
    have hcpos : 0 < cur.length := by
      apply Nat.pos_of_ne_zero; intro h0; apply hl0
      apply BitVec.eq_of_toNat_eq; rw [hblN, h0]; rfl
    have hmx : ¬ (sint.Z (W64 1073741824) < sint.Z b.len) := by
      rw [hblZ, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
    rw [decide_eq_false hmx]
    try wp_auto
    wp_apply hread o b.len _ hoI $$ Hinv Hacc Hosfd Hbs as %r %e %hre %hemp %hPe Hosfd Hbs
    wp_apply wp_string_to_bytes r as %tmp ⟨Htmp, -⟩
    by_cases hr0 : r = []
    · icases ownSlice_len tmp _ _ $$ Htmp with %Htl
      have htl0 : tmp.len = W64 0 := by
        apply BitVec.eq_of_toInt_eq
        rw [hr0] at Htl; simp only [sint.nat, sint.Z] at Htl
        rw [show (W64 0).toInt = 0 from rfl]; simp at Htl; omega
      wp_apply wp_slice_copy_of_len_zero b tmp htl0
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        iapply IH $$ %b %o %n %pre %cur %hk %hb' %ho' %hpl %hcl %hpv Hpre Hcur Hosfd Hbs Hfd HΦ
      · rw [decide_eq_false he4]
        try wp_auto
        by_cases he0 : e = W64 0
        · subst he0
          try wp_auto
          ihave Hsl := hcomb cur $$ [Hpre Hcur]
          · iframe
          iapply HΦ
          iframe
          isplitl []
          · isplitl [] <;> (try isplitl []) <;> iassumption
          obtain ⟨⟨-, hl⟩, hx⟩ := hfin cur rfl
          isplitr
          · ipureintro; exact ⟨hl, by omega, hx⟩
          ileft; ipureintro
          refine .inr ⟨rfl, by omega, fun i bt hh h1 h2 => ?_⟩
          -- `io.EOF`: the empty read at `off + n` reached no held byte, so all are below it
          apply Nat.lt_of_not_le; intro hge
          exact hemp rfl hr0 i bt hh (by omega) (by omega)
        · have he0' : ¬ e = W64 0 := he0
          simp only [decide_eq_false he0', Bool.not_false]
          try wp_auto
          wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn as %pe #Hok
          ihave Hsl := hcomb cur $$ [Hpre Hcur]
          · iframe
          iapply HΦ
          iframe
          isplitl []
          · isplitl [] <;> (try isplitl []) <;> iassumption
          obtain ⟨⟨-, hl⟩, hx⟩ := hfin cur rfl
          isplitr
          · ipureintro; exact ⟨hl, by omega, hx⟩
          iright; iexists pe; iframe Hok; ipureintro; exact ⟨rfl, e, hPe, he0'⟩
    · wp_apply wp_slice_copy b cur tmp r (DFrac.own 1) $$ [Hcur Htmp] as %mm ⟨%hmm, Hcur, -⟩
      · iframe
      have hrl : 0 < r.length := List.length_pos_iff.2 hr0
      have hmmZ : sint.Z mm = min cur.length r.length := by
        simp only [sint.nat, sint.Z] at hmm ⊢; omega
      have hmmN : mm.toNat = min cur.length r.length := by
        rw [← w64_sintNat mm (w64_toNat_of_sintZ mm (by omega)), hmm]
      have hc2l : (r.take cur.length ++ cur.drop r.length).length = cur.length := by
        simp; omega
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        iapply IH $$ %b %o %n %pre %_ %hk %hb' %ho' %hpl %(hc2l.trans hcl) %hpv Hpre Hcur Hosfd Hbs
          Hfd HΦ
      · rw [decide_eq_false he4]
        try wp_auto
        by_cases he0 : e = W64 0
        · subst he0
          have hm0 : mm ≠ W64 0 := by
            intro h; rw [h, show sint.Z (W64 0) = 0 from rfl] at hmmZ; omega
          try wp_auto
          rw [decide_eq_false hm0]
          try wp_auto
          have hmmle : mm.toNat ≤ cur.length := by omega
          have hmmZ' : sint.Z mm = mm.toNat := by rw [hmmZ, hmmN]
          have hmmNat : sint.nat mm = mm.toNat := by rw [hmm, hmmN]
          rw [if_pos ⟨by omega, by omega, Hbwf.2⟩]
          -- the bytes read join the prefix
          icases (ownSlice_split_all mm b (DFrac.own 1) _ ⟨by omega, by omega⟩).1 $$ Hcur
            with ⟨Hc1, Hc2⟩
          have hnZ : sint.Z n = n.toNat := w64_sintZ n hnN
          have hnmN : (n + mm).toNat = n.toNat + mm.toNat := w64_add_toNat _ _ (by omega)
          have hnmZ : sint.Z (n + mm) = n.toNat + mm.toNat := by
            rw [w64_sintZ _ (by omega), hnmN]; simp
          ihave Hc1 := (show slice.slice b w8 (W64 0) mm ↦*
                (r.take cur.length ++ cur.drop r.length).take (sint.nat mm) ⊢
              slice.slice sl w8 n (n + mm) ↦*
                (r.take cur.length ++ cur.drop r.length).take (sint.nat mm) by
            rw [hb', slice_slice sl n sl.len (W64 0) mm ⟨by omega, by omega⟩,
              show n + W64 0 = n from BitVec.add_zero n]) $$ Hc1
          ihave Hpre := (ownSlice_combine n sl (DFrac.own 1) pre _ (W64 0) (n + mm)
            ⟨by rw [w64_sintNat n hnN, hpl, hzn0]; rfl, by decide, by rw [hnZ, hz0]; omega,
              by rw [hnZ, hnmZ]; omega⟩) $$ Hpre Hc1
          have hb'' : slice.slice b w8 mm b.len = slice.slice sl w8 (n + mm) sl.len := by
            rw [hb', slice_slice sl n sl.len mm _ ⟨by omega, by omega⟩]
            congr 1
            show n + (sl.len - n) = sl.len
            rw [BitVec.add_comm, BitVec.sub_add_cancel]
          have ho'' : o + mm = off + (n + mm) := by rw [ho', BitVec.add_assoc]
          have hk' : (n + mm).toNat ≤ vs.length := by omega
          have hpl' : (pre ++ (r.take cur.length ++ cur.drop r.length).take (sint.nat mm)).length =
              (n + mm).toNat := by
            rw [hmmNat]; simp; omega
          have hcl' : ((r.take cur.length ++ cur.drop r.length).drop (sint.nat mm)).length =
              vs.length - (n + mm).toNat := by
            rw [hmmNat]; simp; omega
          have hpv' : ∀ i bt, os.heldByte rs i bt → off.toNat ≤ i → i < off.toNat + (n + mm).toNat →
              (pre ++ (r.take cur.length ++ cur.drop r.length).take (sint.nat mm))[i - off.toNat]? =
                some bt := by
            intro i bt hh h1 h2
            by_cases hlt : i < off.toNat + n.toNat
            · rw [List.getElem?_append_left (by omega)]; exact hpv i bt hh h1 hlt
            · rw [List.getElem?_append_right (by omega), hpl, hmmNat, List.getElem?_take,
                if_pos (by omega), List.getElem?_append_left (by simp; omega), List.getElem?_take,
                if_pos (by omega)]
              rw [show i - off.toNat - n.toNat = i - o.toNat by omega]
              exact hre i bt hh (by omega) (by omega) (by omega)
          try wp_auto
          rw [show b.len - mm = (slice.slice b w8 mm b.len).len from rfl]
          iapply IH $$ %(slice.slice b w8 mm b.len) %(o + mm) %(n + mm) %_ %_ %hk' %hb'' %ho''
            %hpl' %hcl' %hpv' Hpre Hc2 Hosfd Hbs Hfd HΦ
        · have he0' : ¬ e = W64 0 := he0
          simp only [decide_eq_false he0', Bool.not_false]
          try wp_auto
          wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn as %pe #Hok
          ihave Hsl := hcomb _ $$ [Hpre Hcur]
          · iframe
          iapply HΦ
          iframe
          isplitl []
          · isplitl [] <;> (try isplitl []) <;> iassumption
          obtain ⟨⟨-, hl⟩, hx⟩ := hfin _ hc2l
          isplitr
          · ipureintro; exact ⟨hl, by omega, hx⟩
          iright; iexists pe; iframe Hok; ipureintro; exact ⟨rfl, e, hPe, he0'⟩

/-- **`specRacyLt`**: `wp_proofRacyLtQ` at `Pe e := FsNoErr → e = 0` (when `FsNoErr` holds, a
`pread` returns errno 0, `pread_noErr` through `wp_ext_post`), so a `*PathError`, of an errno
`e ≠ 0`, witnesses `¬ FsNoErr`. -/
theorem os.File.ReadAt.wp_proofRacyLt : os.File.ReadAt.specRacyLt (GF := GF) (hG := hG) := by
  intro f fd name dqf sl vs off dq d rs P E eof hrd hoff hn2 hend hE
  iintro %Φ Hpre HΦ
  iapply os.File.ReadAt.wp_proofRacyLtQ (fun e => FsNoErr → e = W64 0)
    (fun fd o n Φ => by
      by_cases hne : FsNoErr
      · obtain ⟨Sio, hS, hs1, -, -⟩ := hne
        haveI := hs1
        iintro H
        iapply wp_ext_post "PRead" _ (by simp [val.isPanic])
          (fun r => ∃ r0, r = PairV r0 (#(0 : w64))) (pread_noErr hS fd o n) Φ
        iapply wp_wand $$ H
        iintro %r H %hr
        iapply H
        ipureintro
        intro r0 e he _
        obtain ⟨r1, hr1⟩ := hr
        rw [hr1] at he
        exact (go.intoVal_inj (val.PairV.inj he).2).symm
      · exact wp_mono (fun _ => by
          iintro H; iapply H; ipureintro; intro _ _ _ h; exact absurd h hne))
    f fd name dqf sl vs off dq d rs P E eof hrd hoff hn2 hend hE $$ Hpre
  inext
  iintro %n %err ⟨Hfo, Hfd, Hbs, %vs', Hsl, %h, Hr⟩
  iapply HΦ
  iframe
  isplitr
  · ipureintro; exact h
  icases Hr with (%h4 | ⟨%pe, %hpe, Hok⟩)
  · ileft; ipureintro; exact h4
  · obtain ⟨hpe1, e, he, hne0⟩ := hpe
    iright; iexists pe; iframe Hok
    ipureintro; exact ⟨hpe1, fun h => hne0 (he h)⟩

/-- **The racing read** (`specRacy`): `specRacyLt`'s post, weakened. -/
theorem os.File.ReadAt.wp_proofRacy : os.File.ReadAt.specRacy (GF := GF) (hG := hG) := by
  intro f fd name dqf sl vs off dq d rs eof hrd hoff hn2 hend
  iintro %Φ Hpre HΦ
  iapply os.File.ReadAt.wp_racyLtOwn os.File.ReadAt.wp_proofRacyLt f fd name dqf sl vs off dq d rs eof
    hrd hoff hn2 hend $$ Hpre
  inext
  iintro %n %err ⟨Hfo, Hfd, Hbs, %vs', Hsl, %h, Hr⟩
  obtain ⟨h1, h2, h3⟩ := h
  iapply HΦ
  iframe
  icases Hr with (%h4 | ⟨%pe, %hpe, -⟩)
  · ipureintro
    refine ⟨h1, h2, h3, ?_⟩
    rcases h4 with h | ⟨he, -, hall⟩
    · exact .inl h
    · exact .inr (.inl ⟨he, hall⟩)
  · ipureintro; exact ⟨h1, h2, h3, .inr (.inr ⟨pe, hpe⟩)⟩

end proof

end EtcdGrove
end Perennial
