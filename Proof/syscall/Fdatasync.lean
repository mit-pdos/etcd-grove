/-
The proof of `Spec/syscall/Fdatasync.lean`: the extension's `Fsync` (`wp_osFsync`, and
`wp_osFsyncB` for the byte-less `specB`), then `errnoErr`.
-/
module

public import Spec.syscall.Fdatasync

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
variable [syscall.Assumptions]

theorem syscall.Fdatasync.wp_proof : syscall.Fdatasync.spec (GF := GF) (hG := hG) := by
  intro fd dq d m lo xs hcov
  wp_start as ⟨#Hinv, Hfd, Hm, Hbs⟩
  wp_apply wp_osFsync fd dq d m lo xs hcov CoPset.subseteq_top $$ Hinv Hfd Hm Hbs as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe

theorem syscall.Fdatasync.wp_proofB : syscall.Fdatasync.specB (GF := GF) (hG := hG) := by
  intro fd dq d m
  wp_start as ⟨#Hinv, Hfd, Hm⟩
  wp_apply wp_osFsyncB fd dq d m CoPset.subseteq_top $$ Hinv Hfd Hm as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
