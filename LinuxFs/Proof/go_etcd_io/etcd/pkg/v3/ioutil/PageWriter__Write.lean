/-
`(*PageWriter).Write` (see `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/ioutil/PageWriter__Write.lean`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.ioutil.PageWriter__Write
public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.ioutil.PageWriter__Flush

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- `Write` when `p` fits below the watermark: it is copied into the buffer (the first branch). -/
theorem ioutil.wp_Write_fits (pw : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF)
    (out pend : List w8) (p : GoSlice) (xs : List w8) (dq : DFrac)
    (hxs : xs.length < 2 ^ 62) (hfit : pend.length + xs.length ≤ 131072) :
    ⊢ io.writerStream wi W -∗
    {{ ioutil.ownPageWriter pw wi pend ∗ W out ∗ p ↦*{dq} xs }}
      (App (Val (pw @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.ty @!!
        go!"Write")) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ⌜err = GoInterface.nil ∧ sint.Z n = xs.length⌝ ∗
        W out ∗ ioutil.ownPageWriter pw wi (pend ++ xs) ∗ p ↦*{dq} xs }} := by
  iintro #Hw
  wp_start as ⟨Hpw, Hout, Hp⟩
  iunfold ioutil.ownPageWriter at Hpw
  icases Hpw with ⟨%v, %bs, Hv, Hbuf, %Hwf⟩
  obtain ⟨Hwv, Hwm, Hok, Hpend⟩ := Hwf
  obtain ⟨w, off, pB, bb, buf, wm⟩ := v
  simp only at Hwv Hwm Hok Hpend
  subst Hwv Hwm Hpend
  dsimp only
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hbwf := ownSlice_wf _ _ _ $$ Hbuf
  ihave %Hplen := ownSlice_len _ _ _ $$ Hp
  ihave %Hpwf := ownSlice_wf _ _ _ $$ Hp
  have hbbw := ioutil.pwOk_bb_le Hok
  obtain ⟨hpB, hpBle, hoff0, hoff1, hbb0, -, -, hlen⟩ := Hok
  simp only [ioutil.wmBytes] at hpBle hbbw hlen
  have hbl : sint.Z buf.len = 131072 + sint.Z pB := by
    have := Hblen.1; word
  have hpl : sint.Z p.len = xs.length := by
    have := Hplen.1; word
  have hm0 := Int.emod_nonneg (sint.Z off + sint.Z bb) (by omega : sint.Z pB ≠ 0)
  have hm1 := Int.emod_lt_of_pos (sint.Z off + sint.Z bb) hpB
  have hbbn : (sint.nat bb : Int) = sint.Z bb := by
    have : sint.nat bb = (sint.Z bb).toNat := rfl; omega
  have hbblt : sint.Z bb ≤ (bs.length : Int) := by omega
  have htk : (bs.take (sint.nat bb)).length = sint.nat bb := by
    rw [List.length_take]; omega
  rw [htk] at hfit
  wp_auto
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by refine ⟨hbb0, ?_, Hbwf.2⟩; omega))]
    have hsp : 0 ≤ sint.Z bb ∧ sint.Z bb ≤ sint.Z buf.len := ⟨hbb0, by omega⟩
    icases (ownSlice_split_all (V := w8) bb buf _ bs hsp).1 $$ Hbuf with ⟨Hb1, Hb2⟩
    wp_auto
    wp_apply wp_slice_copy (V := w8) _ _ p xs dq $$ [Hb2 Hp] as %c ⟨%Hc, Hb2, Hp⟩
    · iframe
    have hdl : xs.length ≤ (bs.drop (sint.nat bb)).length := by
      rw [List.length_drop]; omega
    rw [List.take_of_length_le hdl]
    ihave Hbuf := (ownSlice_split_all (V := w8) bb buf _
      (bs.take (sint.nat bb) ++ (xs ++ (bs.drop (sint.nat bb)).drop xs.length)) hsp).2 $$ [Hb1 Hb2]
    · rw [List.take_left' htk, List.drop_left' htk]; iframe
    wp_auto
    dsimp only
    have hsum : sint.Z (bb + p.len) = sint.Z bb + xs.length := by word
    have hsumn : sint.nat (bb + p.len) = sint.nat bb + xs.length := by
      have : sint.nat (bb + p.len) = (sint.Z (bb + p.len)).toNat := rfl; omega
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, hpl⟩
    iunfold ioutil.ownPageWriter
    iexists _, _
    iframe Hv
    dsimp only
    iframe
    ipureintro
    refine ⟨rfl, rfl, ioutil.pwOk_of_le hpB hpBle hoff0 hoff1 (by omega) (by simp only [ioutil.wmBytes]; omega) ?_, ?_⟩
    · simp only [List.length_append, List.length_take, List.length_drop, ioutil.wmBytes]; omega
    · rw [hsumn, ← List.append_assoc]
      exact (List.take_left' (by rw [List.length_append, htk])).symm
  · exfalso; apply Hif; word

theorem go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.Write.wp_proof
    (wp_Flush : go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.Flush.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.Write.spec (GF := GF) (hG := hG) := by
  intro pw wi W out pend p xs dq hxs
  by_cases hfit : pend.length + xs.length ≤ 131072
  · iintro #Hw
    ihave #Hf := ioutil.wp_Write_fits pw wi W out pend p xs dq hxs hfit $$ Hw
    iintro !> %Φ Hpre HΦ
    iapply Hf $$ Hpre
    iintro !> %n %err ⟨%Hr, Hout, Hpw, Hp⟩
    iapply HΦ
    iexists [], pend ++ xs
    rw [List.append_nil]
    iframe
    ipureintro
    refine ⟨fun _ => ⟨rfl, Hr.2⟩, fun h => absurd Hr.1 h⟩
  iintro #Hw
  wp_start as ⟨Hpw, Hout, Hp⟩
  iunfold ioutil.ownPageWriter at Hpw
  icases Hpw with ⟨%v, %bs, Hv, Hbuf, %Hwf⟩
  obtain ⟨Hwv, Hwm, Hok, Hpend⟩ := Hwf
  obtain ⟨w, off, pB, bb, buf, wm⟩ := v
  simp only at Hwv Hwm Hok Hpend
  subst Hwv Hwm Hpend
  dsimp only
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hbwf := ownSlice_wf _ _ _ $$ Hbuf
  ihave %Hplen := ownSlice_len _ _ _ $$ Hp
  ihave %Hpwf := ownSlice_wf _ _ _ $$ Hp
  have Hok0 := Hok
  have hbbw := ioutil.pwOk_bb_le Hok
  obtain ⟨hpB, hpBle, hoff0, hoff1, hbb0, hal, hun, hlen⟩ := Hok
  simp only [ioutil.wmBytes] at hpBle hbbw hlen hal hun
  have hbl : sint.Z buf.len = 131072 + sint.Z pB := by
    have := Hblen.1; word
  have hpl : sint.Z p.len = xs.length := by
    have := Hplen.1; word
  have hm0 := Int.emod_nonneg (sint.Z off + sint.Z bb) (by omega : sint.Z pB ≠ 0)
  have hm1 := Int.emod_lt_of_pos (sint.Z off + sint.Z bb) hpB
  have hbbn : (sint.nat bb : Int) = sint.Z bb := by
    have : sint.nat bb = (sint.Z bb).toNat := rfl; omega
  have hbblt : sint.Z bb ≤ (bs.length : Int) := by omega
  have htk : (bs.take (sint.nat bb)).length = sint.nat bb := by
    rw [List.length_take]; omega
  rw [htk] at hfit
  wp_auto
  wp_if_destruct
  · exfalso; apply hfit
    have h : sint.Z (p.len + bb) = xs.length + sint.Z bb := by word
    have h2 : sint.Z (W64 131072) = 131072 := by decide
    omega
  simp only [show ¬ (sint.Z pB = 0) by omega, ↓reduceIte]
  wp_auto
  have hsrem : sint.Z (BitVec.srem (off + bb) pB) = (sint.Z off + sint.Z bb) % sint.Z pB := by
    rw [ioutil.sint_srem _ _ (by word)]; congr 1; word
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (k : Nat) (nk : w64) (s' : GoSlice),
        ⌜k ≤ xs.length ∧ sint.Z nk = k⌝ ∗
        n_ptr ↦ nk ∗ p_ptr ↦ s' ∗ s' ↦*{dq} xs.drop k ∗
        (s' ↦*{dq} xs.drop k -∗ p ↦*{dq} xs) ∗
        ioutil.ownPageWriter pw wi (bs.take (sint.nat bb) ++ xs.take k) ∗ W out ∗
        err_ptr ↦ GoInterface.nil ∗ pw_ptr ↦ pw) ∨
      (⌜v = returnVal #()⌝ ∗ n_ptr ↦ (W64 xs.length) ∗ err_ptr ↦ GoInterface.nil ∗ W out ∗
        pw_ptr ↦ pw ∗
        ioutil.ownPageWriter pw wi (bs.take (sint.nat bb) ++ xs) ∗ p ↦*{dq} xs)))
    with [Hv Hbuf Hp Hout n p slack err pw]
  · ileft
    isplitl []
    · itrivial
    iexists 0, (zero_val w64 : w64), p
    rw [List.drop_zero, List.take_zero, List.append_nil]
    iframe n
    iframe p
    iframe Hp
    iframe Hout
    iframe err
    iframe pw
    isplitr
    · ipureintro; exact ⟨by omega, by decide⟩
    isplitr
    · iintro H; iexact H
    iunfold ioutil.ownPageWriter
    iexists _, bs
    iframe Hv
    dsimp only
    iframe
    ipureintro
    exact ⟨rfl, rfl, Hok0, rfl⟩
  · have hm : (sint.Z off + sint.Z bb) % sint.Z pB ≠ 0 := by
      intro h; apply Hif
      have : sint.Z (BitVec.srem (off + bb) pB) = 0 := by rw [hsrem, h]
      word
    have hbm := hun hm
    have hsl0 : sint.Z (pB - BitVec.srem (off + bb) pB) =
        sint.Z pB - (sint.Z off + sint.Z bb) % sint.Z pB := by word
    wp_join (iprop(∃ sl : w64, slack_ptr ↦ sl ∗ p_ptr ↦ p ∗
        ⌜sint.Z sl = min (sint.Z pB - (sint.Z off + sint.Z bb) % sint.Z pB) xs.length⌝))
      with [slack p] as ⟨%sl, slack, p, %Hsl⟩
    · iexists p.len; iframe; ipureintro; omega
    · iexists _; iframe; ipureintro; omega
    have hsl1 : sint.Z sl ≤ xs.length := by omega
    have hsl2 : 0 ≤ sint.Z sl := by omega
    have hroom : sint.Z bb + sint.Z sl ≤ sint.Z buf.len := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z bb ∧ sint.Z bb ≤ sint.Z buf.len ∧
      sint.Z buf.len ≤ sint.Z buf.cap by omega))]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z sl ∧
      sint.Z sl ≤ sint.Z p.cap by refine ⟨by decide, by word, by omega⟩))]
    have hsp : 0 ≤ sint.Z bb ∧ sint.Z bb ≤ sint.Z buf.len := ⟨hbb0, by omega⟩
    have hpsp : 0 ≤ sint.Z sl ∧ sint.Z sl ≤ sint.Z p.len := ⟨hsl2, by omega⟩
    have hsln : (sint.nat sl : Int) = sint.Z sl := by
      have : sint.nat sl = (sint.Z sl).toNat := rfl; omega
    have htks : (xs.take (sint.nat sl)).length = sint.nat sl := by
      rw [List.length_take]; omega
    icases (ownSlice_split_all (V := w8) bb buf _ bs hsp).1 $$ Hbuf with ⟨Hb1, Hb2⟩
    icases (ownSlice_split_all (V := w8) sl p _ xs hpsp).1 $$ Hp with ⟨Hp1, Hp2⟩
    try wp_auto
    wp_apply wp_slice_copy (V := w8) _ _ _ _ dq $$ [Hb2 Hp1] as %c ⟨%Hc, Hb2, Hp1⟩
    · iframe
    have hdl : (xs.take (sint.nat sl)).length ≤ (bs.drop (sint.nat bb)).length := by
      rw [htks, List.length_drop]; omega
    rw [List.take_of_length_le hdl, htks]
    ihave Hbuf := (ownSlice_split_all (V := w8) bb buf _ (bs.take (sint.nat bb) ++
      (xs.take (sint.nat sl) ++ (bs.drop (sint.nat bb)).drop (sint.nat sl))) hsp).2 $$ [Hb1 Hb2]
    · rw [List.take_left' htk, List.drop_left' htk]; iframe
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z sl ∧ sint.Z sl ≤ sint.Z p.len ∧
      sint.Z p.len ≤ sint.Z p.cap by omega))]
    wp_auto
    dsimp only
    have hbbsl : sint.Z (bb + sl) = sint.Z bb + sint.Z sl := by word
    have hbbsln : sint.nat (bb + sl) = sint.nat bb + sint.nat sl := by
      have : sint.nat (bb + sl) = (sint.Z (bb + sl)).toNat := rfl; omega
    have hbs'len : (bs.take (sint.nat bb) ++
        (xs.take (sint.nat sl) ++ (bs.drop (sint.nat bb)).drop (sint.nat sl))).length =
        bs.length := by
      simp only [List.length_append, List.length_take, List.length_drop]; omega
    have htake' : (bs.take (sint.nat bb) ++
        (xs.take (sint.nat sl) ++ (bs.drop (sint.nat bb)).drop (sint.nat sl))).take
          (sint.nat (bb + sl)) = bs.take (sint.nat bb) ++ xs.take (sint.nat sl) := by
      rw [hbbsln, ← List.append_assoc]
      exact List.take_left' (by rw [List.length_append, htk, htks])
    wp_if_destruct
    · -- partial: all of `p` buffered, return
      have hslL : sint.Z sl = xs.length := by omega
      have hslx : xs.take (sint.nat sl) = xs := List.take_of_length_le (by omega)
      have hslw : sl = W64 xs.length := by word
      have hm' : (sint.Z off + sint.Z (bb + sl)) % sint.Z pB =
          (sint.Z off + sint.Z bb) % sint.Z pB + sint.Z sl := by
        rw [hbbsl, ← Int.add_assoc]; exact ioutil.emod_add_small _ _ _ hpB hsl2 (by omega)
      have hm0' := Int.emod_nonneg (sint.Z off + sint.Z bb) (by omega : sint.Z pB ≠ 0)
      iright
      isplitl []
      · itrivial
      rw [← hslw]
      iframe n
      iframe err
      iframe Hout
      iframe pw
      isplitl [Hv Hbuf]
      · iunfold ioutil.ownPageWriter
        iexists _, _
        iframe Hv
        dsimp only
        iframe
        ipureintro
        refine ⟨rfl, rfl, ⟨hpB, hpBle, hoff0, hoff1, by omega,
          fun h => by simp only [ioutil.wmBytes]; omega, fun _ => by simp only [ioutil.wmBytes]; omega,
          by rw [hbs'len]; simp only [ioutil.wmBytes]; omega⟩, ?_⟩
        rw [htake', hslx]
      · iapply (ownSlice_split_all (V := w8) sl p _ xs hpsp).2
        iframe
    · have hslv : sint.Z sl = sint.Z pB - (sint.Z off + sint.Z bb) % sint.Z pB := by omega
      have hm' : (sint.Z off + sint.Z (bb + sl)) % sint.Z pB = 0 := by
        rw [hbbsl, ← Int.add_assoc, hslv]; exact ioutil.emod_add_fill _ _
      ileft
      isplitl []
      · itrivial
      iexists sint.nat sl, sl, slice.slice p w8 sl p.len
      iframe n
      iframe p
      iframe Hp2
      iframe Hout
      iframe err
      iframe pw
      isplitr
      · ipureintro; exact ⟨by omega, by omega⟩
      isplitl [Hp1]
      · iintro H
        iapply (ownSlice_split_all (V := w8) sl p _ xs hpsp).2
        iframe
      iunfold ioutil.ownPageWriter
      iexists _, _
      iframe Hv
      dsimp only
      iframe
      ipureintro
      refine ⟨rfl, rfl, ⟨hpB, hpBle, hoff0, hoff1, by omega,
        fun _ => by simp only [ioutil.wmBytes]; omega, fun h => absurd hm' h,
        by rw [hbs'len]; simp only [ioutil.wmBytes]; omega⟩, htake'.symm⟩
  sorry

end proof

end EtcdGrove
end Perennial
