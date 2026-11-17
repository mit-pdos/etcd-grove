/-
The proof of `Spec/os/File__SyncNoErr.lean`: the model's `EINTR` loop runs once over
`wp_osFsyncBNE` (errno 0), as `Proof/os/File__Sync.lean`'s `wp_proofB` success.
-/
module

public import Spec.os.File__SyncNoErr
public import Proof.os.File__Sync
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

theorem os.File.Sync.wp_proofBNoErr : os.File.Sync.specBNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS f fd name dqf dq d m
  unfold os.ownFile
  wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hm⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFdKind fd dq d CoPset.subseteq_top $$ Hinv Hosfd as Hosfd
  wp_apply wp_osFsyncBNE hS fd dq d m CoPset.subseteq_top $$ Hinv Hosfd Hm as %c Hm Hosfd
  iapply HΦ
  iframe
  isplitl [] <;> iassumption

end proof

end EtcdGrove
end Perennial
