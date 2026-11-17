/-
The proof of `Spec/os/File__StatNoErr.lean`: the model's `EINTR` loop runs once over `wp_osFstatNE`
(errno 0), and the `fileStat` it allocates, as `Proof/os/File__Stat.lean`'s success.
-/
module

public import Spec.os.File__StatNoErr
public import Proof.os.File__Stat
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
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

theorem os.File.Stat.wp_proofNoErr : os.File.Stat.specNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS f fd name dqf dq dqm d m
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hm⟩
  unfold os.model.inner os.model.arbitraryMode
  rw [os.file_ty_eq, os.File_ty_eq, os.fileStat_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFstatNE hS fd dq dqm d m CoPset.subseteq_top $$ Hinv Hosfd Hm as Hosfd Hm
  iapply wp_fupd
  iStructNamed fs
  try wp_auto
  wp_apply os.model.wp_base as %nm _
  try wp_auto
  wp_apply wp_ArbitraryInt as %x _
  ipersist name
  ipersist size
  ipersist mode
  imodintro
  iapply HΦ
  iframe
  isplitl []
  · isplitl [] <;> iassumption
  iexists fs_ptr
  unfold os.ownFileStat
  isplitr
  · ipureintro; rfl
  isplitl []
  · iassumption
  isplitl []
  · iexists _; iassumption
  iexists _
  iassumption

end proof

end EtcdGrove
end Perennial
