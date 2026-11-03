/-
The proof of `Spec/os/File__ReadAt.lean`: the model's loop, by Löb induction over its `EINTR`
retries, with `b` holding anything of its length; a successful `pread` reads every byte, so the
loop then ends at once. The racing read (`wp_proofRacy`): by Löb induction over every iteration,
the arguments named first (`wp_call3_gen`); the invariant splits the slice at `n`, the bytes read
so far (exact at every held byte) and the rest of `b` (anything).
-/
module

public import Spec.os.File__ReadAt

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

theorem os.File.ReadAt.wp_proof : os.File.ReadAt.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf sl vs off dq dqm dqb d m xs hrd hoff hn2 hin hxl
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hm, Hbs⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl _ vs $$ Hsl with %Hlen
  wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_auto
  icases ownSlice_wf sl _ vs $$ Hsl with %Hwf
  have hslz : sint.Z sl.len = vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  clear Hlen
  obtain ⟨cur, hcur⟩ : ∃ cur, cur = vs := ⟨_, rfl⟩
  ihave Hsl := (show sl ↦* vs ⊢ sl ↦* cur by rw [hcur]) $$ Hsl
  have hcl : cur.length = vs.length := by rw [hcur]
  clear hcur
  iloeb as IH generalizing %cur %hcl Hsl Hosfd Hm Hbs Hfd HΦ
  by_cases hl0 : sl.len = W64 0
  · rw [decide_eq_true hl0]
    wp_auto
    have hv0 : vs.length = 0 := by
      rw [hl0, show sint.Z (W64 0) = 0 from rfl] at hslz; omega
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    ipureintro
    refine ⟨hcl, .inl ⟨by rw [hv0]; rfl, rfl, ?_⟩⟩
    rw [List.length_eq_zero_iff.1 (hcl.trans hv0), List.length_eq_zero_iff.1 (hxl.trans hv0)]; rfl
  · rw [decide_eq_false hl0]
    wp_auto
    have hmx : ¬ (sint.Z (W64 1073741824) < sint.Z sl.len) := by
      rw [hslz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
    rw [decide_eq_false hmx]
    wp_auto
    wp_apply wp_osPRead fd off sl.len dq dqm dqb d m xs CoPset.subseteq_top hrd hoff
      (by simp only [sint.Z] at hslz; have := BitVec.toInt_eq_toNat_cond sl.len; split at this <;> omega)
      $$ Hinv Hosfd Hm Hbs as %r %e %hre Hosfd Hm Hbs
    have hrl : r.length ≤ vs.length := by
      rcases hre with ⟨-, rfl⟩ | ⟨-, k, hk, rfl⟩
      · simp [hxl]
      · simp; omega
    wp_apply wp_string_to_bytes r as %tmp ⟨Htmp, -⟩
    wp_apply wp_slice_copy sl cur tmp r (DFrac.own 1) $$ [Hsl Htmp] as %mm ⟨%hmm, Hsl, -⟩
    · iframe
    have hvl : (r.take cur.length ++ cur.drop r.length).length = vs.length := by simp; omega
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      rw [decide_eq_false hl0]
      iapply IH $$ %_ %hvl Hsl Hosfd Hm Hbs Hfd HΦ
    · rw [decide_eq_false he4]
      wp_auto
      rcases hre with ⟨rfl, rfl⟩ | ⟨he0, -⟩
      · rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
        simp only [Bool.not_true]
        have hrl' : (xs.map Prod.fst).length = vs.length := by simp [hxl]
        have hmmv : sint.nat mm = vs.length := by rw [hmm, hcl, hrl']; omega
        have hmm0 : mm ≠ W64 0 := by
          intro h; rw [h, show sint.nat (W64 0) = 0 from rfl] at hmmv
          simp only [sint.Z] at hslz; rw [← hmmv] at hslz
          exact hl0 (BitVec.eq_of_toInt_eq (by rw [hslz]; rfl))
        wp_auto
        rw [decide_eq_false hmm0]
        wp_auto
        have hmmeq : mm = sl.len := by
          apply BitVec.eq_of_toInt_eq
          simp only [sint.nat, sint.Z] at hmmv hslz
          have : vs.length ≠ 0 := by
            intro h; rw [h] at hslz; exact hl0 (BitVec.eq_of_toInt_eq (by rw [hslz]; rfl))
          omega
        rw [hmmeq, if_pos ⟨Hwf.1, Int.le_refl _, Hwf.2⟩]
        wp_auto
        rw [decide_eq_true (show sl.len - sl.len = W64 0 from BitVec.sub_self sl.len),
          show W64 0 + sl.len = sl.len from BitVec.zero_add _]
        wp_auto
        have hsln : sl.len = W64 vs.length := by
          apply BitVec.eq_of_toInt_eq
          simp only [sint.Z] at hslz
          rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          refine ⟨hvl, .inl ⟨hsln, rfl, ?_⟩⟩
          rw [hcl, ← hrl', List.take_length, List.drop_eq_nil_of_le (by rw [hrl', hcl]; exact Nat.le_refl _), List.append_nil]
      · have he0' : ¬ e = W64 0 := he0
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro; exact ⟨hvl, .inr ⟨rfl, by intro h; cases h⟩⟩


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

theorem os.File.ReadAt.wp_proofRacy : os.File.ReadAt.specRacy (GF := GF) (hG := hG) := by
  intro f fd name dqf sl vs off dq d rs eof hrd hoff hn2 hend
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hbs, #Heof⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl _ vs $$ Hsl with %Hlen
  wp_auto
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
  wp_auto
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
    wp_auto
    have hc0 : cur.length = 0 := by rw [← hblN, hl0]; rfl
    ihave Hsl := hcomb cur $$ [Hpre Hcur]
    · iframe
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    ipureintro
    obtain ⟨⟨-, hl⟩, hx⟩ := hfin cur rfl
    exact ⟨hl, by omega, hx, .inl ⟨rfl, by omega⟩⟩
  · rw [decide_eq_false hl0]
    wp_auto
    have hcpos : 0 < cur.length := by
      apply Nat.pos_of_ne_zero; intro h0; apply hl0
      apply BitVec.eq_of_toNat_eq; rw [hblN, h0]; rfl
    have hmx : ¬ (sint.Z (W64 1073741824) < sint.Z b.len) := by
      rw [hblZ, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
    rw [decide_eq_false hmx]
    wp_auto
    wp_apply wp_osPRead_racy_list fd o b.len dq d rs CoPset.subseteq_top hrd hoI
      $$ Hinv Hosfd Hbs as %r %e %hre Hosfd Hbs
    wp_apply wp_string_to_bytes r as %tmp ⟨Htmp, -⟩
    have heof : r = [] → e = 0 → ∀ i bt, os.heldByte rs i bt → off.toNat ≤ i →
        i < off.toNat + vs.length → i < off.toNat + n.toNat := by
      intro hr he i bt hh h1 h2
      apply Classical.byContradiction; intro hge
      obtain ⟨x, hx, hx1, hxb⟩ := hh
      have hk : i - x.1 < x.2.2.length := by
        apply Classical.byContradiction; intro hk
        rw [List.getElem?_eq_none (by omega)] at hxb; cases hxb
      have := (hre x hx (i - x.1) hk (by omega) (by omega)).1 he
      rw [hr] at this; simp at this
    by_cases hr0 : r = []
    · icases ownSlice_len tmp _ _ $$ Htmp with %Htl
      have htl0 : tmp.len = W64 0 := by
        apply BitVec.eq_of_toInt_eq
        rw [hr0] at Htl; simp only [sint.nat, sint.Z] at Htl
        rw [show (W64 0).toInt = 0 from rfl]; simp at Htl; omega
      wp_apply wp_slice_copy_of_len_zero b tmp htl0
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ %b %o %n %pre %cur %hk %hb' %ho' %hpl %hcl %hpv Hpre Hcur Hosfd Hbs Hfd HΦ
      · rw [decide_eq_false he4]
        wp_auto
        by_cases he0 : e = W64 0
        · subst he0
          wp_auto
          ihave Hsl := hcomb cur $$ [Hpre Hcur]
          · iframe
          iapply HΦ
          iframe
          isplitl []
          · isplitl [] <;> iassumption
          ipureintro
          obtain ⟨⟨-, hl⟩, hx⟩ := hfin cur rfl
          exact ⟨hl, by omega, hx, .inr (.inl ⟨rfl, heof hr0 rfl⟩)⟩
        · have he0' : ¬ e = W64 0 := he0
          simp only [decide_eq_false he0', Bool.not_false]
          wp_auto
          wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
          ihave Hsl := hcomb cur $$ [Hpre Hcur]
          · iframe
          iapply HΦ
          iframe
          isplitl []
          · isplitl [] <;> iassumption
          ipureintro
          obtain ⟨⟨-, hl⟩, hx⟩ := hfin cur rfl
          exact ⟨hl, by omega, hx, .inr (.inr ⟨pe, rfl⟩)⟩
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
        wp_auto
        iapply IH $$ %b %o %n %pre %_ %hk %hb' %ho' %hpl %(hc2l.trans hcl) %hpv Hpre Hcur Hosfd Hbs
          Hfd HΦ
      · rw [decide_eq_false he4]
        wp_auto
        by_cases he0 : e = W64 0
        · subst he0
          have hm0 : mm ≠ W64 0 := by
            intro h; rw [h, show sint.Z (W64 0) = 0 from rfl] at hmmZ; omega
          wp_auto
          rw [decide_eq_false hm0]
          wp_auto
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
              obtain ⟨x, hx, hx1, hxb⟩ := hh
              have hk : i - x.1 < x.2.2.length := by
                apply Classical.byContradiction; intro hk
                rw [List.getElem?_eq_none (by omega)] at hxb; cases hxb
              have hidx : x.1 + (i - x.1) - o.toNat = i - o.toNat := by omega
              have hr := (hre x hx (i - x.1) hk (by omega) (by omega)).2 (by omega)
              rw [List.getElem?_eq_getElem hk] at hxb
              simp only [Option.map_some, Option.some.injEq] at hxb
              rw [show i - off.toNat - n.toNat = i - o.toNat by omega, ← hidx,
                List.getElem?_eq_getElem (by omega), hr, hxb]
          wp_auto
          rw [show b.len - mm = (slice.slice b w8 mm b.len).len from rfl]
          iapply IH $$ %(slice.slice b w8 mm b.len) %(o + mm) %(n + mm) %_ %_ %hk' %hb'' %ho''
            %hpl' %hcl' %hpv' Hpre Hc2 Hosfd Hbs Hfd HΦ
        · have he0' : ¬ e = W64 0 := he0
          simp only [decide_eq_false he0', Bool.not_false]
          wp_auto
          wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
          ihave Hsl := hcomb _ $$ [Hpre Hcur]
          · iframe
          iapply HΦ
          iframe
          isplitl []
          · isplitl [] <;> iassumption
          ipureintro
          obtain ⟨⟨-, hl⟩, hx⟩ := hfin _ hc2l
          exact ⟨hl, by omega, hx, .inr (.inr ⟨pe, rfl⟩)⟩


end proof

end EtcdGrove
end Perennial
