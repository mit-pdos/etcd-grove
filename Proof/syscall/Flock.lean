/-
The proof of `Spec/syscall/Flock.lean`: the extension's `Flock` (`wp_osFlock`; for a non-blocking
request or an unlock when `FsNoErr` holds, `wp_osFlockNE`), then `errnoErr`.
-/
module

public import Spec.syscall.Flock
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

theorem syscall.Flock.wp_proof : syscall.Flock.spec (GF := GF) (hG := hG) := by
  intro fd how d req nb hhow hfree
  wp_start as ⟨#Hinv, Hfd, Ht⟩
  by_cases hk : req = none ∨ nb = true
  · by_cases hne : FsNoErr
    · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
      haveI := hs2
      wp_apply wp_osFlockNE hSio fd how d req nb CoPset.subseteq_top hhow hfree hk $$ Hinv Hfd Ht
        as %e %he Hfd
      iapply wp_errno
      iapply HΦ
      iframe
      ipureintro
      intro _
      rcases he with he | he
      · exact Or.inl he
      · exact Or.inr (Or.inl he)
    · wp_apply wp_osFlock fd how d req nb CoPset.subseteq_top hhow hfree $$ Hinv Hfd Ht as %e Hfd
      iapply wp_errno
      iapply HΦ
      iframe
      ipureintro
      exact fun _ => Or.inr (Or.inr hne)
  · wp_apply wp_osFlock fd how d req nb CoPset.subseteq_top hhow hfree $$ Hinv Hfd Ht as %e Hfd
    iapply wp_errno
    iapply HΦ
    iframe
    ipureintro
    exact fun h => absurd h hk

end proof

end EtcdGrove
end Perennial
