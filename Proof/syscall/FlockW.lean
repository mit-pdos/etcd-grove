/-
The proof of `Spec/syscall/FlockW.lean`: by cases on `FsNoErr`, `specNoErr` or `spec`.
-/
module

public import Spec.syscall.FlockW
public import Spec.syscall.FlockNoErr

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

theorem syscall.Flock.wp_proofW
    (hF : syscall.Flock.spec (GF := GF) (hG := hG))
    (hNE : syscall.Flock.specNoErr (GF := GF) (hG := hG)) :
    syscall.Flock.specW (GF := GF) (hG := hG) := by
  intro fd how d req nb hreq hfl hnb
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2⟩ := hne
    haveI := hs2
    iapply hNE Sio hSio fd how d req nb hreq hfl hnb $$ Hpre
    inext
    iintro %e ⟨%he, Hout⟩
    iapply HΦ
    iframe Hout
    ipureintro
    rcases he with he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  · iapply hF fd how d req nb hreq hfl $$ Hpre
    inext
    iintro %e Hout
    iapply HΦ
    iframe Hout
    ipureintro; exact Or.inr (Or.inr hne)

end proof

end EtcdGrove
end Perennial
