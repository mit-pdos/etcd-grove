/-
The proof of `Spec/os/File__SyncS.lean`: the fd's kind (a directory's), then the model's `EINTR`
loop by Löb induction over the shared `DirSync` (`wp_osDirSyncSW`: an errno only when `¬ FsNoErrIno`).
-/
module

public import Proof.os.ForLoeb
public import Proof.os.ErrorOk
public import Spec.os.File__SyncS
public import GooseLang.Ext.Fs.NoIoErrSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.Sync.wp_proofDirS : os.File.Sync.specDirS (GF := GF) (hG := hG) := by
  intro f fd name dqf R j ph n
  unfold os.ownFile
  wp_start as ⟨#Hinv, #Hsi, ⟨%inner, #Hf, Hfd, #Hn, #Hnb, #Hsys⟩, Hd, #Hlb⟩
  ihave #Hf2 := Hf
  iStructNamed Hf2
  try wp_auto
  try wp_auto
  wp_stub os.fsFdKind.impl
  wp_apply wp_osFdKindDirS fd j ph CoPset.subseteq_top $$ Hinv Hd as Hd
  try wp_auto
  wp_for_bind
  iloeb as IH generalizing Hd HΦ
  wp_for_step
  try wp_auto
  wp_stub os.fsDirSync.impl
  wp_apply wp_osDirSyncSW R fd j ph n CoPset.subseteq_top CoPset.subseteq_top
    $$ Hinv Hsi Hd Hlb as %e Hd Hr %hne
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    try wp_auto
    wp_for_post
    inext
    iapply IH $$ Hd HΦ Hfd [$] [$] [$] [$]
  rw [decide_eq_false he4]
  try wp_auto
  by_cases he0 : e = W64 0
  · subst he0
    rw [show decide (W64 0 = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    try wp_auto
    icases Hr with (%he | Hc)
    · exact absurd rfl he
    wp_for_post
    iapply HΦ
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    iright
    iframe
    ipureintro; rfl
  · simp only [decide_eq_false he0, Bool.not_false]
    try wp_auto
    wp_apply os.wp_wrapErrno_ok _ inner name e he0 $$ Hn Hsys as %pe #Hok
    wp_for_post
    iapply HΦ
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    ileft
    iframe Hok
    ipureintro; exact ⟨fun h => (by cases h), hne he0⟩

end proof

end EtcdGrove
end Perennial
