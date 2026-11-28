/-
(hraft_robust R3) The proof of `disk.Fresh`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Fresh
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.raftFile
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__persist

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Fresh.wp_proof
    (wp_raftFile : github_com.hashicorp.raft.examples.hraftnet.disk.raftFile.spec (GF := GF) (hG := hG))
    (wp_persist : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.persist.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Fresh.spec (GF := GF) (hG := hG) := by
  intro γd f R qc dir Wl Ws Wf s hf hname
  iintro %Φ #Hpkg #Hos #Hsh #Hdi Hds Hdh Hcp HWf HΦ
  wp_func_call
  wp_call
  try wp_auto
  wp_apply (lc := 1) wp_raftFile
  rw [← hname]
  try wp_auto
  iStructNamed «$r0»
  ihave Hmem := diskMem0_empty «$r0_ptr» $$ [ents keys vals ikeys ivals staged commit]
  · iunfold diskMem0; iframe
  rw [show (⟨[], [], [], W64 0⟩ : DiskImg) = emptyImg from rfl]
  imod (disk_boot_fresh γd f R Wl Ws Wf s ⊤) $$ Hds HWf with ⟨%g, %Hg, #Hinv, Htk, Hl, Hs, Hrec⟩
  obtain ⟨hgd, hgf, hgR⟩ := Hg
  subst hgd hgf hgR
  ipersist file
  wp_bind (App (Val #(methods (go.GoType.PointerType Disk.ty) go!"persist" #«$r0_ptr»)) (Val #()))
  iapply (wp_persist g «$r0_ptr» emptyImg (W64 0) qc) $$ Hpkg file [] Hos Hsh Hdi Hmem Hdh Hcp
  · ipureintro; exact hf
  iapply (freshWriteAU g Wl Ws Wf _) $$ Hinv Hrec Hlc1
  iintro Hrec HWf Hdh Hcp Hmem
  iapply wp_fupd
  imod sync.init_Mutex (diskLockInv g «$r0_ptr») ⊤ «$v0_ptr» $$ [«$v0»] [Hmem Hrec Hdh Hcp] with #Hmu
  · iexact «$v0»
  · inext; iunfold diskLockInv; iexists emptyImg, W64 0, qc; iframe; ipureintro; exact emptyImg_ok
  ipersist mu
  try wp_auto
  imodintro
  iapply HΦ $$ %g %«$r0_ptr» [] [] Htk Hl Hs HWf
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  · iunfold isDisk; iexists «$v0_ptr»; iframe #; ipureintro; exact hf

end sec

end Perennial
