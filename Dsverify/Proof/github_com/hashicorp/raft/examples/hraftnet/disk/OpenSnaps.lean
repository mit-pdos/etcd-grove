/-
(hraft_robust R3) The proof of `disk.OpenSnaps` (`snap.go`), as `examples/snapstore`'s.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.OpenSnaps
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.snapFile
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__decode
public import Dsverify.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Read

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

theorem github_com.hashicorp.raft.examples.hraftnet.disk.OpenSnaps.wp_proof
    (wp_snapFile : github_com.hashicorp.raft.examples.hraftnet.disk.snapFile.spec (GF := GF) (hG := hG))
    (wp_decode : github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.decode.spec (GF := GF) (hG := hG))
    (wp_Read : github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.OpenSnaps.spec (GF := GF) (hG := hG) := by
  intro γd f R qc dir Qc Wf v lat svs hf hname hv
  obtain ⟨S, hok, rfl, hm⟩ := hv
  iintro %Φ #Hpkg #Hos #Hsh #Hdi Hds Hdh Hcp HΦ
  ihave #Hdur : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable $$ []
  · iPkgInit
  wp_func_call
  wp_call
  try wp_auto
  wp_apply wp_snapFile
  rw [← hname]
  wp_bind (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Read)) _)
  iapply (wp_wand_r (Φ := fun w => iprop(⌜w = DurFs.readRes (some (encSnap S))⌝ ∗
    DurFs.durSt γd ⟨some (encSnap S), none⟩ ∗ DurFs.durHandle γd f R ∗ Fs.osCallPerm (Fs.callKey R f.d) qc)))
  isplitl [Hds Hdh Hcp]
  · iapply (wp_Read γd f R qc hf) $$ Hdur Hos Hsh Hdi Hdh Hcp
    iauintro
    unfold atomic_acc
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask from Std.LawfulSet.empty_subset)
    iintro Hclose
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists ⟨some (encSnap S), none⟩
    iframe Hds
    isplit
    · iintro Hds; imod Hclose with -; imodintro; iframe
    · iintro Hds; imod Hclose with -; imodintro; iintro Hdh Hcp; iframe; ipureintro; rfl
  iintro %w ⟨%Hw, Hds, Hdh, Hcp⟩
  subst Hw
  try wp_auto
  simp only [Option.isSome_some, Bool.not_true]
  try wp_auto
  wp_apply wp_snapFile
  rw [← hname]
  try wp_auto
  wp_apply (wp_string_to_bytes (encSnap S)) as %b ⟨Hb, -⟩
  ihave >#Hb := ownSlice_persist b _ _ $$ Hb
  iStructNamed «$r0»
  iapply wp_fupd
  wp_apply (wp_decode «$r0_ptr» b S hok) $$ [has meta' data nextID] as Hmem
  · iframe #; iunfold snapsMem0; iexists zeroValDef, slice.nil, W64 0; iframe; ipureintro; rfl
  icases snapsMem_at _ _ $$ Hmem with ⟨%has, %mv, %dt, Hmem⟩
  icases snapMem_lat _ _ _ _ _ $$ Hmem with ⟨Hmem, #Hr, %Hmv⟩
  imod (snap_boot γd f R Qc Wf S hok (latOfMem S.latest mv) ⊤) $$ Hds Hr with ⟨%g, %Hg, #Hinv, Htk, Hl, Hrec⟩
  obtain ⟨hgd, hgf, hgR⟩ := Hg
  subst hgd hgf hgR
  imod sync.init_Mutex (snapsLockInv g «$r0_ptr») ⊤ «$v0_ptr» $$ [«$v0»] [Hmem Hrec Hdh Hcp] with #Hmu
  · iexact «$v0»
  · inext; iunfold snapsLockInv; iexists latOfMem S.latest mv, S.latest, S.nextID, has, mv, dt, qc
    iframe; iframe #; ipureintro; exact Hmv
  ipersist mu
  ipersist file
  try wp_auto
  imodintro
  iapply HΦ $$ %g %«$r0_ptr» %(latOfMem S.latest mv) [] [] Htk Hl []
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  · iunfold isSnaps; iexists «$v0_ptr»; iframe #; ipureintro; exact hf
  · iapply latEquiv_of lat _ S.latest svs hm; iexact Hr

end proof

end Perennial
