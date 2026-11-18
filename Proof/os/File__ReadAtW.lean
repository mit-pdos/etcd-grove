/-
The proof of `Spec/os/File__ReadAtW.lean`: by cases on `FsNoErr`, `specRacyLtNoErr` (no error) or
`specRacyLt` (its error arm with the case's `¬ FsNoErr`).
-/
module

public import Spec.os.File__ReadAtW
public import Spec.os.File__ReadAtNoErr

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
variable [os.Assumptions]

theorem os.File.ReadAt.wp_proofRacyLtW
    (hR : os.File.ReadAt.specRacyLt (GF := GF) (hG := hG))
    (hNE : os.File.ReadAt.specRacyLtNoErr (GF := GF) (hG := hG)) :
    os.File.ReadAt.specRacyLtW (GF := GF) (hG := hG) := by
  intro f fd name dqf sl vs off dq d rs eof hrd hoff hn2 hend
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs1
    iapply hNE Sio hSio f fd name dqf sl vs off dq d rs eof hrd hoff hn2 hend $$ Hpre
    inext
    iintro %n %err ⟨Hfo, Hfd, Hbs, %vs', Hsl, %h⟩
    iapply HΦ
    iframe Hfo Hfd Hbs
    iexists vs'
    iframe Hsl
    isplitr
    · ipureintro; exact ⟨h.1, h.2.1, h.2.2.1⟩
    ileft; ipureintro; exact h.2.2.2
  · iapply hR f fd name dqf sl vs off dq d rs eof hrd hoff hn2 hend $$ Hpre
    inext
    iintro %n %err ⟨Hfo, Hfd, Hbs, %vs', Hsl, %h, Hr⟩
    iapply HΦ
    iframe Hfo Hfd Hbs
    iexists vs'
    iframe Hsl
    isplitr
    · ipureintro; exact h
    icases Hr with (%h4 | ⟨%pe, %hpe, #Hok⟩)
    · ileft; ipureintro; exact h4
    · iright; iexists pe; iframe Hok
      ipureintro; exact ⟨hpe, hne⟩

end proof

end EtcdGrove
end Perennial
