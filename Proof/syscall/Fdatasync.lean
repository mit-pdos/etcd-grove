/-
The proof of `Spec/syscall/Fdatasync.lean`: the extension's `Fsync` (`wp_osFsync`, and
`wp_osFsyncB` for the byte-less `specB`, by cases on `FsNoErr`: `wp_osFsyncBNE` when it holds,
errno 0), then `errnoErr`.
-/
module

public import Spec.syscall.Fdatasync
public import GooseLang.Ext.Fs.NoErrSpecsOpen

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

theorem syscall.Fdatasync.wp_proof : syscall.Fdatasync.spec (GF := GF) (hG := hG) := by
  intro fd dq d m lo xs hcov
  wp_start as ⟨#Hinv, Hfd, Hm, Hbs⟩
  by_cases hne : FsNoErrIno
  · obtain ⟨Sio, hSio, hs1, -, -⟩ := hne
    try wp_auto
    wp_stub syscall.fsFsync.impl
    wp_apply wp_osFsyncNE (Sio := Sio) hSio fd dq d m lo xs hcov CoPset.subseteq_top $$ Hinv Hfd Hm Hbs
      as Hm Hbs Hfd
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ
    iframe Hfd
    ileft
    iframe
    ipureintro; rfl
  · try wp_auto
    wp_stub syscall.fsFsync.impl
    wp_apply wp_osFsync fd dq d m lo xs hcov CoPset.subseteq_top $$ Hinv Hfd Hm Hbs as %e Hr Hfd
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ
    iframe Hfd
    icases Hr with (H | ⟨%he, Hm, Hbs⟩)
    · ileft; iexact H
    · iright; iframe Hm Hbs; ipureintro; exact ⟨he.1, he.2, hne⟩

theorem syscall.Fdatasync.wp_proofB : syscall.Fdatasync.specB (GF := GF) (hG := hG) := by
  intro fd dq d m
  wp_start as ⟨#Hinv, Hfd, Hm⟩
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs1
    try wp_auto
    wp_stub syscall.fsFsync.impl
    wp_apply wp_osFsyncBNE hSio fd dq d m CoPset.subseteq_top $$ Hinv Hfd Hm as %c Hm Hfd
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ
    iframe Hfd
    ileft
    isplitr
    · ipureintro; rfl
    iexists c; iexact Hm
  · try wp_auto
    wp_stub syscall.fsFsync.impl
    wp_apply wp_osFsyncB fd dq d m CoPset.subseteq_top $$ Hinv Hfd Hm as %e Hr Hfd
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ
    iframe Hfd
    icases Hr with (H | ⟨%he, Hm⟩)
    · ileft; iexact H
    · iright; iframe Hm; ipureintro; exact ⟨he.1, he.2, hne⟩

end proof

end EtcdGrove
end Perennial
