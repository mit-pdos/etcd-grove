/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/preallocExtend.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtendTrunc
public import LinuxFs.Spec.os.File__Fd
public import LinuxFs.Proof.syscall.FileOps
public import Perennial.Proof.errors.As

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
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend.wp_proof
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_trunc : go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtendTrunc.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m o sz hfd hwr hmaps ho0 ho1 hsz0 hsz1 hle
  wp_start as ⟨#Hinv, #Herrs, Hf, Ho, Hfd, Hm⟩
  wp_auto
  wp_apply wp_Fd f fd name dqf $$ Hf as Hf
  have htg : max m.size ((W64 0).toNat + sz.toNat) = sz.toNat := by
    rw [show (W64 0).toNat = 0 from rfl]; omega
  wp_apply syscall.Fallocate.wp_grow fd (W64 0) sz dq d m hwr (by decide) hsz0
    $$ [Hfd Hm] as %e ⟨Hfd, %n, Hr⟩
  · iframe; iframe Hinv; rw [htg]; iapply mcellsAny_empty (GF := GF) _ hmaps
  have htg' : max m.size (0 + sz.toNat) = sz.toNat := by omega
  by_cases he : e = 0
  · subst he
    icases Hr with (⟨-, Hd⟩ | ⟨%hne, -⟩)
    rotate_left
    · exact absurd rfl hne
    rw [show errnoErr (0 : w64) = interface.nil from ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    wp_auto
    iapply HΦ
    iframe
    iexists sz.toNat
    isplitr
    · ipureintro; exact ⟨hle, Nat.le_refl _, fun _ => rfl⟩
    have hp : rsDone (GF := GF) false d.ino (max m.size (0 + sz.toNat)) (max m.size (0 + sz.toNat)) m n ⊢
        preGrown (GF := GF) d.ino m sz.toNat := by
      have := rsDone_preGrown (GF := GF) (tr := false) d.ino (max m.size (0 + sz.toNat))
        (max m.size (0 + sz.toNat)) m n (Or.inr rfl)
      rw [htg'] at this ⊢; exact this
    iapply hp $$ Hd
  icases Hr with (⟨%h0, -⟩ | ⟨-, Hr⟩)
  · exact absurd h0 he
  ihave Hg : ∃ w0, ⌜m.size ≤ w0 ∧ w0 ≤ sz.toNat⌝ ∗ preGrown (GF := GF) d.ino m w0 $$ [Hr]
  · icases Hr with (Hu | ⟨%w, %hw, Hd⟩)
    · iexists m.size
      isplitr
      · ipureintro; exact ⟨Nat.le_refl _, hle⟩
      iapply rsUndone_preGrown $$ Hu
    · iexists w
      isplitr
      · ipureintro; omega
      iapply rsDone_preGrown (hsz := Or.inl hw.1) $$ Hd
  icases Hg with ⟨%w0, %hw0, Hg⟩
  rw [show errnoErr e = interface.ok ⟨syscall.Errno.ty, #e⟩ from if_neg he]
  wp_auto
  ihave #Htree := errno_errTree (GF := GF) e
  wp_apply errors.As.wp_proof (· = interface.ok ⟨syscall.Errno.ty, #e⟩)
      (interface.ok ⟨syscall.Errno.ty, #e⟩) errno_ptr (T' := w64) (T := syscall.Errno.ty)
      (zero_val w64) errno_asTarget $$ [errno] as %b %v' Herrno
  · iframe; isplitr; · iexact Htree
    ipureintro; rfl
  cases b
  · wp_auto
    iapply HΦ
    iframe Hf Ho Hfd
    iexists w0
    iframe Hg
    ipureintro; exact ⟨hw0.1, hw0.2, fun h => by cases h⟩
  · wp_auto
    by_cases h95 : v' = W64 95
    · subst h95
      wp_auto
      icases (preGrown_unfold _ _ _).1 $$ Hg with ⟨%m1, %hm1, Hm1, Hz⟩
      obtain ⟨rfl, hmm, hcz1, hg1⟩ := hm1
      wp_apply wp_trunc f fd name dqf dq d m1 o sz hfd hwr (hmm.trans hmaps) ho0 ho1 (by omega)
          hsz1 hw0.2 $$ [Hf Ho Hfd Hm1] as %err ⟨Hf, Ho, Hfd, %w, %hw, Hg'⟩
      · iframe; iexact Hinv
      iapply HΦ
      iframe Hf Ho Hfd
      iexists w
      isplitr
      · ipureintro; exact ⟨by omega, hw.2.1, hw.2.2⟩
      iapply preGrown_trans d.ino m m1 w hw0.1 hw.1 hmm hcz1 hg1 $$ [Hz Hg']
      iframe
    · try rw [decide_eq_false h95]
      try wp_auto
      by_cases h4 : v' = W64 4
      · subst h4
        wp_auto
        icases (preGrown_unfold _ _ _).1 $$ Hg with ⟨%m1, %hm1, Hm1, Hz⟩
        obtain ⟨rfl, hmm, hcz1, hg1⟩ := hm1
        wp_apply wp_trunc f fd name dqf dq d m1 o sz hfd hwr (hmm.trans hmaps) ho0 ho1 (by omega)
            hsz1 hw0.2 $$ [Hf Ho Hfd Hm1] as %err ⟨Hf, Ho, Hfd, %w, %hw, Hg'⟩
        · iframe; iexact Hinv
        iapply HΦ
        iframe Hf Ho Hfd
        iexists w
        isplitr
        · ipureintro; exact ⟨by omega, hw.2.1, hw.2.2⟩
        iapply preGrown_trans d.ino m m1 w hw0.1 hw.1 hmm hcz1 hg1 $$ [Hz Hg']
        iframe
      · try rw [decide_eq_false h4]
        wp_auto
        iapply HΦ
        iframe Hf Ho Hfd
        iexists w0
        iframe Hg
        ipureintro; exact ⟨hw0.1, hw0.2, fun h => by cases h⟩

end proof

end EtcdGrove
end Perennial
