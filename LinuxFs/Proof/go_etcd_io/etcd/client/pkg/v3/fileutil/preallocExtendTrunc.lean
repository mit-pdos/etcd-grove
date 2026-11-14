/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/preallocExtendTrunc.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtendTrunc
public import LinuxFs.Proof.os.OffEnd
public import LinuxFs.Spec.os.File__Truncate

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
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [os.file.FieldAssumptions]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtendTrunc.wp_proof
    (wp_Truncate : os.File.Truncate.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtendTrunc.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m o sz hfd hwr hmaps ho0 ho1 hsz0 hsz1 hle
  wp_start as ⟨#Hinv, Hf, Ho, Hfd, Hm⟩
  wp_auto
  wp_apply os.File.Seek.wp_cur f fd name dqf o hfd ho0 ho1 $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  have hszN : (sz.toNat : Int) = sz.toInt := by
    have := BitVec.toInt_eq_toNat_cond sz; split at this <;> omega
  have hmsz : m.size ≤ 0xffffffff000 := by omega
  wp_apply os.File.Seek.wp_endOff f fd name dqf o sz dq (DFrac.own 1) d m hfd hmsz hsz0 hsz1
    $$ [Hf Ho Hfd Hm] as %n %err ⟨Hf, Hfd, Hm, Hr⟩
  · iframe; iexact Hinv
  icases Hr with (⟨%hn, Ho⟩ | ⟨%herr, Ho⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    wp_auto
    iapply HΦ
    iframe Hf Ho Hfd
    iexists m.size
    isplitr
    · ipureintro; exact ⟨Nat.le_refl _, hle, fun h => by cases h⟩
    iapply preGrown_same _ _ _ (fun h => absurd h.1 herr) $$ Hm
  obtain ⟨rfl, hfit, rfl⟩ := hn
  wp_auto
  wp_apply os.File.Seek.wp_start f fd name dqf _ o hfd ho0 ho1 $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  have hn : sint.Z (W64 (m.size : Int) + sz) = m.size + sz.toInt := by
    have : sz.toInt ≤ 0xffffffff000 := hsz1
    word
  rw [decide_eq_false (show ¬ sint.Z (W64 (m.size : Int) + sz) < sint.Z sz by
    rw [hn, show sint.Z sz = sz.toInt from rfl]; omega)]
  wp_auto
  ihave Hb0 : osBytes (GF := GF) d.ino (min m.size sz.toNat) (DFrac.own 1) [] $$ []
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  wp_apply wp_Truncate f fd name dqf sz dq d m [] hfd hwr hsz0 (by simp; omega)
    $$ [Hf Hfd Hm Hb0] as %err ⟨Hf, Hfd, Hr, -⟩
  · iframe; iframe Hinv; iapply mcellsAny_empty (GF := GF) _ hmaps
  iapply HΦ
  iframe Hf Ho Hfd
  icases Hr with (⟨%he, Hd⟩ | ⟨%he, (Hd | Hd)⟩)
  · iexists sz.toNat
    isplitr
    · ipureintro; exact ⟨hle, Nat.le_refl _, fun _ => rfl⟩
    iapply ftDone_preGrown _ _ _ _ (fun h => h.2) $$ Hd
  · iexists sz.toNat
    isplitr
    · ipureintro; exact ⟨hle, Nat.le_refl _, fun _ => rfl⟩
    iapply ftDone_preGrown _ _ _ _ (fun h => h.2) $$ Hd
  · iexists m.size
    isplitr
    · ipureintro; exact ⟨Nat.le_refl _, hle, fun h => absurd h he⟩
    iapply preGrown_mono _ _ _ (fun h => absurd h.1 he)
    iapply ftUndone_preGrown $$ Hd

end proof

end EtcdGrove
end Perennial
