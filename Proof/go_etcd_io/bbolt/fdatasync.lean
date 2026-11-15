/-
The proof of `Spec/go_etcd_io/bbolt/fdatasync.lean`: U4 (`notes/bbolt-proof-plan.md`), over `os.File.Fd` and
`syscall.Fdatasync` (its byte-less `specB`: bbolt holds none of the file's bytes here), with `errnoErrOk` (`Mmap/Infra`: a failed sync's errno is `fmtErrorOk`).
-/
module

public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync
public import Proof.go_etcd_io.bbolt.Mmap.Infra

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
  wp_auto
  wp_apply hFd f fd p.path dq $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  wp_apply hSync fd dq ⟨i, true, true⟩ m $$ [Hfd Hm] as %e ⟨Hfd, Hr⟩
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
      · iapply hErr e he.1

end proof

end bbolt
end EtcdGrove
end Perennial
