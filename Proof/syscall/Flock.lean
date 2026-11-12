/-
The proof of `Spec/syscall/Flock.lean`: the extension's `Flock` (`wp_osFlock`), then `errnoErr`.
-/
module

public import Spec.syscall.Flock

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

theorem syscall.Flock.wp_proof : syscall.Flock.spec (GF := GF) (hG := hG) := by
  intro fd how dq d
  wp_start as ⟨#Hinv, Hfd⟩
  wp_apply wp_osFlock fd how dq d CoPset.subseteq_top $$ Hinv Hfd as %e Hfd
  iapply wp_errno
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
