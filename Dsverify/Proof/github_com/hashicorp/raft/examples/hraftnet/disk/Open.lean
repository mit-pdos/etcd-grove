/-
(hraft_robust R3) The proof of `disk.Open`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Open
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.BootLemmas
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.raftFile
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__decode
public import Dsverify.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Read

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

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Open.wp_proof
    (wp_raftFile : github_com.hashicorp.raft.examples.hraftnet.disk.raftFile.spec (GF := GF) (hG := hG))
    (wp_decode : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.decode.spec (GF := GF) (hG := hG))
    (wp_Read : github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Open.spec (GF := GF) (hG := hG) := by
  intro γd f R qc dir Wl Ws Wf v D hf hname hv
  obtain ⟨I, hok, rfl, habs⟩ := hv
  iintro %Φ #Hpkg #Hos #Hsh #Hdi Hds Hdh Hcp HΦ
  ihave #Hdur : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable $$ []
  · iPkgInit
  wp_func_call
  wp_call
  try wp_auto
  wp_apply wp_raftFile
  rw [← hname]
  wp_bind (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Read)) _)
  iapply (wp_wand_r (Φ := fun w => iprop(⌜w = DurFs.readRes (some (encImg I))⌝ ∗
    DurFs.durSt γd ⟨some (encImg I), none⟩ ∗ DurFs.durHandle γd f R ∗ Fs.osCallPerm (Fs.callKey R f.d) qc)))
  isplitl [Hds Hdh Hcp]
  · iapply (wp_Read γd f R qc hf) $$ Hdur Hos Hsh Hdi Hdh Hcp
    iauintro
    unfold atomic_acc
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask from Std.LawfulSet.empty_subset)
    iintro Hclose
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists ⟨some (encImg I), none⟩
    iframe Hds
    isplit
    · iintro Hds; imod Hclose with -; imodintro; iframe
    · iintro Hds; imod Hclose with -; imodintro; iintro Hdh Hcp; iframe; ipureintro; rfl
  iintro %w ⟨%Hw, Hds, Hdh, Hcp⟩
  subst Hw
  try wp_auto
  simp only [Option.isSome_some, Bool.not_true]
  try wp_auto
  wp_apply wp_raftFile
  rw [← hname]
  try wp_auto
  wp_apply (wp_string_to_bytes (encImg I)) as %b ⟨Hb, -⟩
  ihave >#Hb := ownSlice_persist b _ _ $$ Hb
  iStructNamed «$r0»
  iapply wp_fupd
  wp_apply (wp_decode «$r0_ptr» b I hok) $$ [ents keys vals ikeys ivals staged commit] as Hmem
  · iunfold diskMem0; iframe; iframe #
  imod (disk_boot γd f R Wl Ws Wf I hok ⊤) $$ Hds with ⟨%g, %Hg, #Hinv, Htk, Hl, Hs, Hrec⟩
  obtain ⟨hgd, hgf, hgR⟩ := Hg
  subst hgd hgf hgR
  imod sync.init_Mutex (diskLockInv g «$r0_ptr») ⊤ «$v0_ptr» $$ [«$v0»] [Hmem Hrec Hdh Hcp] with #Hmu
  · iexact «$v0»
  · inext; iunfold diskLockInv; iexists I, W64 0, qc; iframe; ipureintro; exact hok
  ipersist mu
  ipersist file
  try wp_auto
  imodintro
  iapply HΦ $$ %g %«$r0_ptr» [] [] Htk [Hl] [Hs]
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  · iunfold isDisk; iexists «$v0_ptr»; iframe #; ipureintro; exact hf
  · rw [← habs, show (absImg I).L = I.absL (W64 0) from rfl]; iexact Hl
  · rw [← habs, show (absImg I).S = I.absS from rfl]; iexact Hs

end sec

end Perennial
