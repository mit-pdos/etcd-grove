/-
The proof of `Spec/os/File__Sync.lean`: the model's `EINTR` loop runs once over `wp_osFsync` (`wp_osFsyncB` for
the byte-less `specB`), which never fails with `EINTR`.
-/
module

public import Proof.os.ErrorOk
public import Spec.os.File__Sync
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
variable [os.Assumptions]

theorem os.File.Sync.wp_proof : os.File.Sync.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m lo xs hcov
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb, #Hap, #Hsys⟩, Hosfd, Hm, Hbs⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_stub os.fsFdKind.impl
  wp_apply wp_osFdKind fd dq d CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  wp_for
  wp_stub os.fsFsync.impl
  wp_apply wp_osFsync fd dq d m lo xs hcov CoPset.subseteq_top $$ Hinv Hosfd Hm Hbs as %e Hr Hosfd
  by_cases he4 : e = W64 4
  · icases Hr with (⟨%he, -, -⟩ | ⟨%he, -, -⟩)
    · exact absurd (he4 ▸ he) (by decide)
    · exact absurd he4 he.2
  rw [decide_eq_false he4]
  try wp_auto
  icases Hr with (⟨%he, Hm, Hbs⟩ | ⟨%he, Hm, Hbs⟩)
  · subst he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    try wp_auto
    wp_for_post
    ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
    iapply HΦ
    iframe Hokn
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    ileft
    isplitr; · ipureintro; rfl
    iframe
  · have he0' : ¬ e = W64 0 := he.1
    simp only [decide_eq_false he0', Bool.not_false]
    try wp_auto
    wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn Hsys as %pe #Hok
    try wp_auto
    wp_for_post
    ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
    iapply HΦ
    iframe Hokn
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    iright
    iframe
    ipureintro; intro h; cases h

/-- `os.File.Sync.specB` without the error witness (session S6: a helper of the proof below). -/
private abbrev os.File.Sync.tripleOldB : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ ∃ c, osMeta d.ino (DFrac.own 1) (m.bsynced c)) ∨
       (⌜err ≠ interface.nil⌝ ∗ osMeta d.ino (DFrac.own 1) m)) ∗
      fmtErrorOkOrNil err }}

/-- `os.File.Sync.specB` over a semantics with no errors (the former `os.File.Sync.specBNoErr`). -/
private abbrev os.File.Sync.tripleNEB : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ RET #(interface.nil : GoInterface); os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ∃ c, osMeta d.ino (DFrac.own 1) (m.bsynced c) }}

private theorem os.File.Sync.wp_oldB : os.File.Sync.tripleOldB (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb, #Hap, #Hsys⟩, Hosfd, Hm⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_stub os.fsFdKind.impl
  wp_apply wp_osFdKind fd dq d CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  wp_for
  wp_stub os.fsFsync.impl
  wp_apply wp_osFsyncB fd dq d m CoPset.subseteq_top $$ Hinv Hosfd Hm as %e Hr Hosfd
  by_cases he4 : e = W64 4
  · icases Hr with (⟨%he, -⟩ | ⟨%he, -⟩)
    · exact absurd (he4 ▸ he) (by decide)
    · exact absurd he4 he.2
  rw [decide_eq_false he4]
  try wp_auto
  icases Hr with (⟨%he, Hm⟩ | ⟨%he, Hm⟩)
  · subst he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    try wp_auto
    wp_for_post
    ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
    iapply HΦ
    iframe Hokn
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    ileft
    isplitr; · ipureintro; rfl
    iframe
  · have he0' : ¬ e = W64 0 := he.1
    simp only [decide_eq_false he0', Bool.not_false]
    try wp_auto
    wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn Hsys as %pe #Hok
    try wp_auto
    wp_for_post
    ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
    iapply HΦ
    iframe Hokn
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    iright
    iframe
    ipureintro; intro h; cases h

private theorem os.File.Sync.wp_NEB : os.File.Sync.tripleNEB (GF := GF) (hG := hG) := by
  intro Sio _ hS f fd name dqf dq d m
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb, #Hap, #Hsys⟩, Hosfd, Hm⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_stub os.fsFdKind.impl
  wp_apply wp_osFdKind fd dq d CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  wp_for
  wp_stub os.fsFsync.impl
  wp_apply wp_osFsyncBNE hS fd dq d m CoPset.subseteq_top $$ Hinv Hosfd Hm as %c Hm Hosfd
  try wp_auto
  wp_for_post
  iapply HΦ
  iframe
  (repeat' isplitl []) <;> iassumption

/-- **`specB`**: by cases on `FsNoErr`, the error-free triple or the one without the witness, whose
error arm then has `¬ FsNoErr`. -/
theorem os.File.Sync.wp_proofB : os.File.Sync.specB (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs1
    iapply os.File.Sync.wp_NEB Sio hSio f fd name dqf dq d m $$ Hpre
    inext
    iintro ⟨Hfo, Hfd, %c, Hm⟩
    iapply HΦ
    iframe Hfo Hfd
    isplitl [Hm]
    · ileft; isplitr
      · ipureintro; rfl
      iexists c; iexact Hm
    · simp only [fmtErrorOkOrNil]; itrivial
  · iapply os.File.Sync.wp_oldB f fd name dqf dq d m $$ Hpre
    inext
    iintro %err ⟨Hfo, Hfd, Hr, #Hok⟩
    iapply HΦ
    iframe Hfo Hfd Hok
    icases Hr with (H | ⟨%he, Hm⟩)
    · ileft; iexact H
    · iright; iframe Hm; ipureintro; exact ⟨he, hne⟩

end proof

end EtcdGrove
end Perennial
