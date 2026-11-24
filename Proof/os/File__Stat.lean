/-
The proof of `Spec/os/File__Stat.lean`: the model's `EINTR` loop over `wp_osFstat`, and the `fileStat` it allocates, which
needs `fileStat.FieldAssumptions` (`TrustedCode/os.lean`).
-/
module

public import Proof.internal.gomodel.LocalChoose
public import Proof.os.ModelMode
public import Proof.os.ForLoeb
public import Proof.os.ErrorOk
public import Proof.os.PathParent
public import Spec.os.File__Stat
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

/-- `os.File.Stat.spec` as it was without the error witness (session S6: a helper of the proof below). -/
private abbrev os.File.Stat.tripleOld : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq dqm : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino dqm m }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Stat")) (Val #()))
  {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err);
      os.ownFile f fd name dqf ∗ osFd fd dq d ∗ osMeta d.ino dqm m ∗
      ((∃ fs : Loc, ⌜err = interface.nil ∧
          fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
          os.ownFileStat fs (W64 m.size)) ∨
       ⌜err ≠ interface.nil ∧ fi = interface.nil⌝) ∗
      fmtErrorOkOrNil err ∗
      (⌜err = GoInterface.nil⌝ ∨ ∃ e : w64, ⌜e ≠ 0⌝ ∗ os.errnoPathErr err e) }}

/-- `os.File.Stat.spec` over a semantics with no errors on every inode (the former `os.File.Stat.specNoErr`). -/
private abbrev os.File.Stat.tripleNE : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq dqm : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino dqm m }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Stat")) (Val #()))
  {{ (fi : GoInterface), RET (PairV #fi #(interface.nil : GoInterface));
      os.ownFile f fd name dqf ∗ osFd fd dq d ∗ osMeta d.ino dqm m ∗
      ∃ fs : Loc, ⌜fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
        os.ownFileStat fs (W64 m.size) }}

private theorem os.File.Stat.wp_old : os.File.Stat.tripleOld (GF := GF) (hG := hG) := by
  intro f fd name dqf dq dqm d m
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb⟩, Hosfd, Hm⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  try wp_auto
  wp_for_bind
  iloeb as IH generalizing Hosfd Hm Hfd HΦ
  wp_for_step
  try wp_auto
  wp_stub os.fsFstat.impl
  wp_apply wp_osFstat fd dq dqm d m CoPset.subseteq_top $$ Hinv Hosfd Hm as %sz %e %hr Hosfd Hm
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    try wp_auto
    try rw [os.fileStat_ty_eq]
    wp_for_post
    inext
    iapply IH $$ Hosfd Hm Hfd HΦ [$] [$] [$] [$]
  · rw [decide_eq_false he4]
    try wp_auto
    rcases hr with ⟨rfl, rfl⟩ | ⟨he0, rfl⟩
    · rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
      simp only [Bool.not_true]
      iapply wp_fupd
      try wp_auto
      iStructNamed «$r0»
      try wp_auto
      wp_apply filepathlite.Base.wp_lex as %nm _
      try wp_auto
      wp_apply os.wp_modelMode as %x
      ipersist name
      ipersist size
      ipersist mode
      imodintro
      ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
      wp_for_post
      iapply HΦ
      iframe Hokn
      iframe
      isplitl []
      · isplitl [] <;> (try isplitl []) <;> iassumption
      isplitr
      rotate_left
      · ileft; ipureintro; rfl
      ileft
      iexists «$r0_ptr»
      unfold os.ownFileStat
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitl []
      · iassumption
      isplitl []
      · iexists _; iassumption
      iexists _
      iassumption
    · have he0' : ¬ e = W64 0 := he0
      rw [decide_eq_false he0']
      try wp_auto
      wp_apply os.wp_wrapErrno_errno _ inner name e $$ Hn as %perr #Hep
      ihave #Hok := os.errnoPathErr_fmtErrorOk perr e he0' $$ Hep
      ihave %Hne := os.errnoPathErr_ne perr e $$ Hep
      ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
      wp_for_post
      iapply HΦ
      iframe Hokn
      iframe
      isplitl []
      · isplitl [] <;> (try isplitl []) <;> iassumption
      isplitr
      rotate_left
      · iright; iexists e; iframe Hep; ipureintro; exact he0'
      iright
      ipureintro; exact ⟨Hne, rfl⟩

private theorem os.File.Stat.wp_NE : os.File.Stat.tripleNE (GF := GF) (hG := hG) := by
  intro Sio _ hS f fd name dqf dq dqm d m
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb⟩, Hosfd, Hm⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  try wp_auto
  wp_for_bind
  iloeb as IH generalizing Hosfd Hm Hfd HΦ
  wp_for_step
  try wp_auto
  wp_stub os.fsFstat.impl
  wp_apply wp_osFstatNE hS fd dq dqm d m CoPset.subseteq_top $$ Hinv Hosfd Hm as Hosfd Hm
  try wp_auto
  try rw [show decide ((0 : w64) = W64 4) = false from decide_eq_false (by decide)]
  try wp_auto
  try rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
  try simp only [Bool.not_true]
  iapply wp_fupd
  iStructNamed «$r0»
  try wp_auto
  wp_apply filepathlite.Base.wp_lex as %nm _
  try wp_auto
  wp_apply os.wp_modelMode as %x
  ipersist name
  ipersist size
  ipersist mode
  imodintro
  wp_for_post
  iapply HΦ
  iframe
  isplitl []
  · isplitl [] <;> (try isplitl []) <;> iassumption
  iexists «$r0_ptr»
  unfold os.ownFileStat
  isplitr
  · ipureintro; rfl
  isplitl []
  · iassumption
  isplitl []
  · iexists _; iassumption
  iexists _
  iassumption

/-- **`os.File.Stat.spec`**: by cases on `FsNoErr`, the error-free triple (`FsNoErr`'s set of inodes, its
step premises) or the triple without the witness, whose error arm then has `¬ FsNoErr`. -/
theorem os.File.Stat.wp_proof : os.File.Stat.spec (GF := GF) (hG := hG) := by
  have hS := os.File.Stat.wp_old (GF := GF) (hG := hG)
  have hNE := os.File.Stat.wp_NE (GF := GF) (hG := hG)
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
