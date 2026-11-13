/-
`(*PageWriter).flush` (see `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/ioutil/PageWriter__flush.lean`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.ioutil.PageWriter__flush

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

theorem go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.flush.wp_proof :
    go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.flush.spec (GF := GF) (hG := hG) := by
  intro pw wi W out pend
  iintro #Hw
  wp_start as ⟨Hpw, Hout⟩
  iunfold ioutil.ownPageWriter at Hpw
  icases Hpw with ⟨%v, %bs, Hv, Hbuf, %Hwf⟩
  obtain ⟨Hwv, Hwm, Hok, Hpend⟩ := Hwf
  obtain ⟨w, off, pB, bb, buf, wm⟩ := v
  simp only at Hwv Hwm Hok Hpend
  subst Hwv Hwm Hpend
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hbwf := ownSlice_wf _ _ _ $$ Hbuf
  simp only at Hblen Hbwf
  have hbbw := ioutil.pwOk_bb_le Hok
  obtain ⟨hpB, hpBle, hoff0, hoff1, hbb0, -, -, hlen⟩ := Hok
  simp only [ioutil.wmBytes] at hpBle hbbw hlen
  have hbl : sint.Z buf.len = 131072 + sint.Z pB := by
    have := Hblen.1; word
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iexists []
    rw [List.append_nil]
    iframe Hout
    isplitr
    · ipureintro; simp
    iunfold ioutil.ownPageWriter
    iexists _, bs
    iframe Hv
    dsimp only
    iframe
    ipureintro
    refine ⟨rfl, rfl, ioutil.pwOk_of_le hpB hpBle hoff0 hoff1 (by word) (by word) hlen, by simp⟩
  · have hbblen : sint.Z bb ≤ sint.Z buf.len := by
      have := Int.emod_nonneg (sint.Z off + sint.Z bb) (by omega : sint.Z pB ≠ 0)
      have := Int.emod_lt_of_pos (sint.Z off + sint.Z bb) hpB
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by refine ⟨by decide, ?_, ?_⟩ <;> word))]
    icases (ownSlice_split_all bb buf _ bs ⟨hbb0, hbblen⟩).1 $$ Hbuf with ⟨Hb1, Hb2⟩
    wp_auto
    unfold io.writerStream
    wp_apply Hw $$ [Hout Hb1] as %n %err ⟨%ys, %Hys, Hout, Hb1⟩
    · iframe
    ihave Hbuf := (ownSlice_split_all bb buf _ bs ⟨hbb0, hbblen⟩).2 $$ [Hb1 Hb2]
    · iframe
    simp only [show ¬ (sint.Z pB = 0) by omega, ↓reduceIte]
    wp_auto
    have hsrem : sint.Z (BitVec.srem (off + bb) pB) = (sint.Z off + sint.Z bb) % sint.Z pB := by
      rw [ioutil.sint_srem _ _ (by word)]; congr 1; word
    have hm0 := Int.emod_nonneg (sint.Z off + sint.Z bb) (by omega : sint.Z pB ≠ 0)
    have hm1 := Int.emod_lt_of_pos (sint.Z off + sint.Z bb) hpB
    iapply HΦ
    iexists ys
    iframe Hout
    isplitr
    · ipureintro; exact Hys
    iunfold ioutil.ownPageWriter
    iexists _, bs
    iframe Hv
    dsimp only
    iframe
    ipureintro
    refine ⟨rfl, rfl, ioutil.pwOk_of_le hpB hpBle (by omega) (by omega) (by word) (by word) hlen,
      by simp⟩

end proof

end EtcdGrove
end Perennial
