/-
The proof of `Spec/syscall/Fdatasync.lean`: the extension's `Fsync` (`wp_Fsync`), then `errnoErr`.
-/
module

public import Spec.syscall.Fdatasync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [syscall.Assumptions]

theorem syscall.Fdatasync.wp_proof : syscall.Fdatasync.spec (GF := GF) (hG := hG) := by
  intro fd dq d m lo xs
  wp_start as ⟨#Hinv, Hfd, Hm, Hbs⟩
  wp_apply wp_Fsync fd dq d m lo xs CoPset.subseteq_top $$ Hinv Hfd Hm Hbs as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
