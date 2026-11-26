/-
The proof of `Spec/go_etcd_io/bbolt/fdatasync.lean`: U4 (`notes/bbolt-proof-plan.md`), over `os.File.Fd` and
`syscall.Fdatasync` (its byte-less `specB`: bbolt holds none of the file's bytes here), with `errnoErrOk` (`Mmap/Infra`: a failed sync's errno is `fmtErrorOk`).
-/
module

public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Spec.os.CrashStILA

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem fdatasync.wp_proof (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hSync : syscall.Fdatasync.specB (GF := GF) (hG := hG))
    (hErr : errnoErrOk (GF := GF) (hG := hG)) :
    fdatasync.spec (GF := GF) (hG := hG) := by
  intro db f fd p i m dqf dq
  wp_start as ⟨#Hos, Hf, Hfo, Hfd, Hm⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  wp_auto
  wp_apply hFd f fd p.path dq $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  wp_apply hSync fd dq (dbFd i) m $$ [Hfd Hm] as %e ⟨Hfd, Hr⟩
  · iframe; iframe #
  ihave Hfo : fileOwn f fd p.path dq $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  icases Hr with (⟨%he, %c, Hm⟩ | ⟨%he, Hm⟩)
  · subst he
    iapply HΦ
    iframe Hf Hfd Hfo
    isplitl [Hm]
    · iexists m.bsynced c; iframe; ipureintro; exact ⟨rfl, rfl⟩
    · ileft; ipureintro; simp [errnoErr]
  · iapply HΦ
    iframe Hf Hfd Hfo
    isplitl [Hm]
    · iexists _; iframe; ipureintro; exact ⟨rfl, rfl⟩
    · iright
      isplitr
      · ipureintro; simp only [errnoErr, he.1, ↓reduceIte]; exact fun h => nomatch h
      · iapply hErr e he.1 $$ Hsys

/-- `fdatasync.specC`'s proof: `os.File.Fd`, then `wp_bFdatasyncC` (the crash-mode sync whose
value moves to idle, `syscall.Fdatasync.specCrashILA`). -/
theorem fdatasync.wp_proofC (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hSA : syscall.Fdatasync.specCrashILA (GF := GF) (hG := hG)) :
    fdatasync.specC (GF := GF) (hG := hG) := by
  intro db f fd p c C' C m o ys dqf dq hc hns ho hys
  wp_start as ⟨#Hos, #Hinv, Hf, Hfo, Hfd, Hm, Hys⟩
  wp_auto
  wp_apply hFd f fd p.path dq $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  wp_apply wp_bFdatasyncC hSA fd dq (dbFd p.ino) p c hc C' C m o ys rfl hns ho hys
    $$ [Hfd Hm Hys] as %e ⟨Hfd, %he, Hr⟩
  · iframe; iframe #
  subst he
  ihave Hfo : fileOwn f fd p.path dq $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  iapply HΦ
  iframe Hf Hfd Hfo Hr
  ipureintro; simp [errnoErr]

end proof

end bbolt
end EtcdGrove
end Perennial
