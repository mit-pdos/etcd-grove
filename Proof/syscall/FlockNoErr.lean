/-
The proof of `Spec/syscall/FlockNoErr.lean`: the extension's `Flock` with no error
(`wp_osFlockNE`), then `errnoErr`.
-/
module

public import Spec.syscall.FlockNoErr
public import GooseLang.Ext.Fs.NoMapLockErrSpecs

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

theorem syscall.Flock.wp_proofNoErr : syscall.Flock.specNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS fd how d req nb hhow hfree hk
  wp_start as ⟨#Hinv, Hfd, Ht⟩
  wp_apply wp_osFlockNE hS fd how d req nb CoPset.subseteq_top hhow hfree hk $$ Hinv Hfd Ht
    as %e %he Hfd
  iapply wp_errno
  iapply HΦ
  iframe
  ipureintro; exact he

end proof

end EtcdGrove
end Perennial
