/-
The proof of `Spec/os/File__WriteAtW.lean`: by cases on `FsNoErr`, `specNoErr` or `spec`.
-/
module

public import Spec.os.File__WriteAtW
public import Spec.os.File__WriteAtNoErr

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

theorem os.File.WriteAt.wp_proofW
    (hW : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hNE : os.File.WriteAt.specNoErr (GF := GF) (hG := hG)) :
    os.File.WriteAt.specW (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d m xs hw hoff hsz hend hpos hlen hxs
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs1
    iapply hNE Sio hSio f fd name dqf sl data dqs off dq d m xs hw hoff hsz hend hpos hlen hxs
      $$ Hpre
    inext
    iintro ⟨Hfo, Hsl, Hfd, %ys, %hys, Hm, Hb, Hc⟩
    iapply HΦ
    iframe Hfo Hsl Hfd
    iexists data.length, ys
    iframe Hm Hb Hc
    isplitr
    · ipureintro
      exact ⟨Nat.le_refl _, hys, ⟨Or.inr (Or.inl rfl), Or.inr hend⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · iapply fmtErrorOkOrNil_nil
  · have hend' : off.toNat + data.length < 2 ^ 63 := by
      have : maxBytes < 2 ^ 63 := by decide
      omega
    iapply hW f fd name dqf sl data dqs off dq d m xs hw hoff hsz hend' hpos hlen hxs $$ Hpre
    inext
    iintro %n %err ⟨Hfo, Hsl, Hfd, %j, %ys, %h, Hm, Hb, Hc, #Hok⟩
    iapply HΦ
    iframe Hfo Hsl Hfd
    iexists j, ys
    iframe Hm Hb Hc Hok
    ipureintro
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    rcases h.2.2.2 with h4 | h4
    · exact Or.inl h4
    · exact Or.inr ⟨h4.1, h4.2, hne⟩

end proof

end EtcdGrove
end Perennial
