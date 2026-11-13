/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/preallocFixed.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.preallocFixed
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

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.preallocFixed.wp_proof
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.preallocFixed.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d sz hwr hsz0
  wp_start as ⟨#Hinv, #Herrs, Hf, Hfd⟩
  wp_auto
  wp_apply wp_Fd f fd name dqf $$ Hf as Hf
  wp_apply syscall.Fallocate.wp_keep fd (W64 0) sz dq d hwr (by decide) hsz0
    $$ [Hfd] as %e Hfd
  · iframe; iexact Hinv
  by_cases he : e = 0
  · subst he
    rw [show errnoErr (0 : w64) = interface.nil from ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    wp_auto
    iapply HΦ
    iframe
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
    iframe
  · wp_auto
    by_cases h95 : v' = W64 95
    · subst h95
      wp_auto
      iapply HΦ
      iframe
    · try rw [decide_eq_false h95]
      wp_auto
      iapply HΦ
      iframe

end proof

end EtcdGrove
end Perennial
