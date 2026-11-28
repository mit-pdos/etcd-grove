/-
(hraft_robust R3) The proof of `disk.FreshSnaps` (`snap.go`), as `examples/snapstore`'s.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.FreshSnaps
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.snapFile
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__persist

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.disk.FreshSnaps.wp_proof
    (wp_snapFile : github_com.hashicorp.raft.examples.hraftnet.disk.snapFile.spec (GF := GF) (hG := hG))
    (wp_persist : github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.persist.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.FreshSnaps.spec (GF := GF) (hG := hG) := by
  intro γd f R qc dir Qc Wf st hf hname
  iintro %Φ #Hpkg #Hos #Hsh #Hdi Hds Hdh Hcp HWf HΦ
  wp_func_call
  wp_call
  try wp_auto
  wp_apply (lc := 1) wp_snapFile
  rw [← hname]
  try wp_auto
  iStructNamed «$r0»
  ihave Hmem : snapsMemAt «$r0_ptr» emptySnap false zeroValDef slice.nil $$ [has meta' data nextID]
  · unfold snapsMemAt emptySnap; iframe; ipureintro; rfl
  imod (snap_boot_fresh γd f R Qc Wf st ⊤) $$ Hds HWf with ⟨%g, %Hg, #Hinv, Htk, Hl, Hrec⟩
  obtain ⟨hgd, hgf, hgR⟩ := Hg
  subst hgd hgf hgR
  ipersist file
  wp_bind (App (Val #(methods (go.GoType.PointerType Snaps.ty) go!"persist" #«$r0_ptr»)) (Val #()))
  iapply (wp_persist g «$r0_ptr» emptySnap false zeroValDef slice.nil qc) $$ Hpkg file [] Hos Hsh Hdi Hmem Hdh Hcp
  · ipureintro; exact hf
  iapply (freshSnapWriteAU g Qc Wf _) $$ Hinv Hrec Hlc1
  iintro Hrec HWf Hdh Hcp Hmem
  iapply wp_fupd
  simp only [emptySnap]
  imod sync.init_Mutex (snapsLockInv g «$r0_ptr») ⊤ «$v0_ptr» $$ [«$v0»] [Hmem Hrec Hdh Hcp] with #Hmu
  · iexact «$v0»
  · inext; iunfold snapsLockInv; iexists none, none, W64 0, false, zeroValDef, slice.nil, qc; iframe
    simp only [latRep, latMv]
    isplit <;> itrivial
  ipersist mu
  try wp_auto
  imodintro
  iapply HΦ $$ %g %«$r0_ptr» [] [] Htk Hl HWf
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  · iunfold isSnaps; iexists «$v0_ptr»; iframe #; ipureintro; exact hf

end proof

end Perennial
