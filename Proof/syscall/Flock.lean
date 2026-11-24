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
  by_cases hne : FsNoErrIno
  · by_cases hk : req = none ∨ nb = true
    · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
      haveI := hs2
      try wp_auto
      wp_stub syscall.fsFlock.impl
      wp_apply wp_osFlockNE hSio fd how d req nb CoPset.subseteq_top hhow hfree hk $$ Hinv Hfd Ht
        as %e %he Hfd
      try wp_auto
      wp_apply wp_errnoErr
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      rcases he with he | ⟨hr, he⟩
      · exact Or.inl he
      · refine Or.inr (Or.inl ⟨hr, ?_, he⟩)
        rcases hk with hk | hk
        · exact absurd hk hr
        · exact hk
    · -- a blocking lock request: errno 0 or a wait (`flockW_noErr`)
      obtain ⟨ex, rfl⟩ : ∃ ex, req = some ex := by
        cases req with
        | none => exact absurd (Or.inl rfl) hk
        | some ex => exact ⟨ex, rfl⟩
      have hnb : nb = false := by cases nb <;> simp_all
      subst hnb
      try wp_auto
      wp_stub syscall.fsFlock.impl
      wp_apply wp_osFlockW fd how d ex CoPset.subseteq_top hhow (hfree (by simp)) $$ Hinv Hfd Ht
        as %e %he Hfd
      try wp_auto
      wp_apply wp_errnoErr
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      by_cases h0 : e = 0
      · exact Or.inl h0
      · exact absurd hne (he h0)
  · try wp_auto
    wp_stub syscall.fsFlock.impl
    wp_apply wp_osFlock fd how d req nb CoPset.subseteq_top hhow hfree $$ Hinv Hfd Ht as %e Hfd
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact Or.inr (Or.inr hne)

end proof

end EtcdGrove
end Perennial
