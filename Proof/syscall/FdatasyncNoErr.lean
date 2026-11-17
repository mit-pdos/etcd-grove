/-
The proof of `Spec/syscall/FdatasyncNoErr.lean`: `wp_osFsyncBNE`, then `errnoErr`.
-/
module

public import Spec.syscall.FdatasyncNoErr
public import Proof.syscall.Fdatasync
public import GooseLang.Ext.Fs.NoErrSpecsOpen

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

theorem syscall.Fdatasync.wp_proofBNoErr :
    syscall.Fdatasync.specBNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS fd dq d m
  wp_start as ⟨#Hinv, Hfd, Hm⟩
  wp_apply wp_osFsyncBNE hS fd dq d m CoPset.subseteq_top $$ Hinv Hfd Hm as %c Hm Hfd
  iapply wp_errno
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
