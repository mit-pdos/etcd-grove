/-
The proof of `Spec/os/File__StatW.lean`: by cases on `FsNoErr`, `specNoErr` or `spec` (its error arm
with the case's `¬ FsNoErr`).
-/
module

public import Spec.os.File__StatW
public import Spec.os.File__StatNoErr

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

theorem os.File.Stat.wp_proofW
    (hS : os.File.Stat.spec (GF := GF) (hG := hG))
    (hNE : os.File.Stat.specNoErr (GF := GF) (hG := hG)) :
    os.File.Stat.specW (GF := GF) (hG := hG) := by
  intro f fd name dqf dq dqm d m
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs1
    iapply hNE Sio hSio f fd name dqf dq dqm d m $$ Hpre
    inext
    iintro %fi ⟨Hfo, Hfd, Hm, %fs, %hfi, Hfs⟩
    iapply HΦ
    iframe Hfo Hfd Hm
    isplitl [Hfs]
    · ileft; iexists fs; iframe Hfs; ipureintro; exact ⟨rfl, hfi⟩
    isplitr
    · iapply fmtErrorOkOrNil_nil
    · ileft; ipureintro; rfl
  · iapply hS f fd name dqf dq dqm d m $$ Hpre
    inext
    iintro %fi %err ⟨Hfo, Hfd, Hm, Hr, #Hok, Hpe⟩
    iapply HΦ
    iframe Hfo Hfd Hm Hok Hpe
    icases Hr with (⟨%fs, %h, Hfs⟩ | %h)
    · ileft; iexists fs; iframe Hfs; ipureintro; exact h
    · iright; ipureintro; exact ⟨h.1, h.2, hne⟩

end proof

end EtcdGrove
end Perennial
