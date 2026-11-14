/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/preallocExtendAu.lean`:
`preallocExtend.lean`'s, the growth by `syscall.Fallocate.wp_growAuW`, the fallback by
`preallocExtendTrunc.specAu`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtendAu
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtendTruncAu
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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend.wp_proofAu
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_trunc : go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtendTrunc.specAu (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend.specAu (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m o sz K P hfd hwr hmaps ho0 ho1 hsz0 hsz1 hle hP
  unfold fallocSup
  wp_start as ⟨#Hinv, #Herrs, Hf, Ho, Hfd, Hm, HK, #Hfs, #Hts⟩
  wp_auto
  wp_apply wp_Fd f fd name dqf $$ Hf as Hf
  have htg : max m.size ((W64 0).toNat + sz.toNat) = sz.toNat := by
    rw [show (W64 0).toNat = 0 from rfl]; omega
  ihave Hau := Hfs $$ %m %hle %(hP m (Nat.le_refl _) hle) HK Hm
  wp_apply syscall.Fallocate.wp_growAuW fd (W64 0) sz dq d m
    (fun _ e => iprop(fallocOutH d.ino sz.toNat m e ∗ K)) hwr (by decide) hsz0 hmaps
    $$ [Hfd Hau] as %e ⟨Hfd, %n, Hr, HK⟩
  · iframe; iframe Hinv; rw [htg]; iexact Hau
  icases fallocOutH_preGrownH d.ino m sz.toNat e hle $$ Hr with ⟨%w0, %hw0, Hg⟩
  by_cases he : e = 0
  · subst he
    rw [show errnoErr (0 : w64) = interface.nil from ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    wp_auto
    iapply HΦ
    have hw : w0 = sz.toNat := hw0.2.2 rfl
    subst hw
    iframe Hf Ho Hfd HK
    iexists sz.toNat
    isplitr
    · ipureintro; exact ⟨hle, Nat.le_refl _, fun _ => rfl⟩
    iapply preGrownH_mono _ _ _ (fun h => ⟨rfl, h.2⟩) $$ Hg
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
    iframe Hf Ho Hfd HK
    iexists w0
    isplitr
    · ipureintro; exact ⟨hw0.1, hw0.2.1, fun h => by cases h⟩
    iapply preGrownH_mono _ _ _ (fun h => by cases h.1) $$ Hg
  · wp_auto
    by_cases h95 : v' = W64 95
    · subst h95
      wp_auto
      iunfold preGrownH at Hg
      icases Hg with ⟨%m1, %hm1, Hm1, Hz⟩
      obtain ⟨rfl, hmm, hcz1, hg1, hpc1, hlo1, -⟩ := hm1
      wp_apply wp_trunc f fd name dqf dq d m1 o sz K P hfd hwr (hmm.trans hmaps) ho0 ho1 (by omega)
          hsz1 hw0.2.1 (fun m' h h' => hP m' (by omega) h') $$ [Hf Ho Hfd Hm1 HK] as %err ⟨Hf, Ho, Hfd, HK, %w, %hw, Hg'⟩
      · iframe; iframe Hinv; iexact Hts
      iapply HΦ
      iframe Hf Ho Hfd HK
      iexists w
      isplitr
      · ipureintro; exact ⟨by omega, hw.2.1, hw.2.2⟩
      iapply preGrownH_trans d.ino m m1 w _ hw0.1 hw.1 hmm hcz1 hg1 hpc1 hlo1 $$ [Hz Hg']
      iframe Hz
      iapply preGrownH_mono _ _ _ (fun h => ⟨h.1, hg1.2.2 h.2.zfGe⟩) $$ Hg'
    · try rw [decide_eq_false h95]
      try wp_auto
      by_cases h4 : v' = W64 4
      · subst h4
        wp_auto
        iunfold preGrownH at Hg
        icases Hg with ⟨%m1, %hm1, Hm1, Hz⟩
        obtain ⟨rfl, hmm, hcz1, hg1, hpc1, hlo1, -⟩ := hm1
        wp_apply wp_trunc f fd name dqf dq d m1 o sz K P hfd hwr (hmm.trans hmaps) ho0 ho1 (by omega)
            hsz1 hw0.2.1 (fun m' h h' => hP m' (by omega) h') $$ [Hf Ho Hfd Hm1 HK] as %err ⟨Hf, Ho, Hfd, HK, %w, %hw, Hg'⟩
        · iframe; iframe Hinv; iexact Hts
        iapply HΦ
        iframe Hf Ho Hfd HK
        iexists w
        isplitr
        · ipureintro; exact ⟨by omega, hw.2.1, hw.2.2⟩
        iapply preGrownH_trans d.ino m m1 w _ hw0.1 hw.1 hmm hcz1 hg1 hpc1 hlo1 $$ [Hz Hg']
        iframe Hz
        iapply preGrownH_mono _ _ _ (fun h => ⟨h.1, hg1.2.2 h.2.zfGe⟩) $$ Hg'
      · try rw [decide_eq_false h4]
        wp_auto
        iapply HΦ
        iframe Hf Ho Hfd HK
        iexists w0
        isplitr
        · ipureintro; exact ⟨hw0.1, hw0.2.1, fun h => by cases h⟩
        iapply preGrownH_mono _ _ _ (fun h => by cases h.1) $$ Hg

end proof

end EtcdGrove
end Perennial
