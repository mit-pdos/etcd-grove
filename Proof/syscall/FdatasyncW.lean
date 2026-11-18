/-
The proof of `Spec/syscall/FdatasyncW.lean`: by cases on `FsNoErr`, `specBNoErr` or `specB`.
-/
module

public import Spec.syscall.FdatasyncW
public import Spec.syscall.FdatasyncNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [syscall.Assumptions]

theorem syscall.Fdatasync.wp_proofBW
    (hF : syscall.Fdatasync.specB (GF := GF) (hG := hG))
    (hNE : syscall.Fdatasync.specBNoErr (GF := GF) (hG := hG)) :
    syscall.Fdatasync.specBW (GF := GF) (hG := hG) := by
  intro fd dq d m
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2⟩ := hne
    haveI := hs1
    iapply hNE Sio hSio fd dq d m $$ Hpre
    inext
    iintro ⟨Hfd, %c, Hm⟩
    iapply HΦ
    iframe Hfd
    ileft
    isplitr
    · ipureintro; rfl
    iexists c; iexact Hm
  · iapply hF fd dq d m $$ Hpre
    inext
    iintro %e ⟨Hfd, Hr⟩
    iapply HΦ
    iframe Hfd
    icases Hr with (H | ⟨%he, Hm⟩)
    · ileft; iexact H
    · iright; iframe Hm; ipureintro; exact ⟨he.1, he.2, hne⟩

end proof

end EtcdGrove
end Perennial
