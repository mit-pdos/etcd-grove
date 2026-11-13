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
  · exfalso; apply hfit
    have h : sint.Z (p.len + bb) = xs.length + sint.Z bb := by word
    have h2 : sint.Z (W64 131072) = 131072 := by decide
    omega
  sorry

end proof

end EtcdGrove
end Perennial
