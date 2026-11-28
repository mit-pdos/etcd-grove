/-
(hraft_robust R3) The proof of `disk.(*Disk).persist`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__persist
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__encode
public import Dsverify.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Write

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

/-- `durWriteSync`'s result weakened. -/
theorem dk_writeSync_wand (γ : DurFs.DurGS) (P Q : IProp GF) :
    DurFs.durWriteSync (GF := GF) γ P ∗ (P -∗ Q) ⊢ DurFs.durWriteSync γ Q := by
  iintro ⟨H, HW⟩ Hnc
  ihave H := H $$ Hnc
  iapply DurFs.durAupd_wand_post
  iframe H
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iintro %_ ⟨Hnc, HP⟩
  iframe Hnc
  iapply HW $$ HP

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.persist.wp_proof
    (wp_encode : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.encode.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.persist.spec (GF := GF) (hG := hG) := by
  intro g d I stg qc
  iintro %Φ #Hpkg #Hfile %Hf #Hos #Hsh #Hdi Hmem Hdh Hcp HAU
  ihave #Hdur : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable $$ []
  · iPkgInit
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_encode $$ [$Hmem] as %b ⟨Hmem, Hb, -⟩
  ihave %Hbl := ownSlice_length_lt_maxAddr_of_cells (V := w8) (fun l v => typedPointsto_split l v _) b _ $$ Hb
  have hlen : (encImg I).length < 2 ^ 63 := by
    have : (2 : Int) ^ 47 < 2 ^ 63 := by decide
    have hm : maxAddr = 2 ^ 47 := rfl
    omega
  wp_apply wp_bytes_to_string b (encImg I) (DFrac.own 1) $$ [$Hb] as -
  try wp_auto
  wp_bind (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Write)) _) _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = #()⌝ ∗ (diskMem d I stg -∗ Φ #()))))
  isplitl [HAU Hdh Hcp]
  · iapply (wp_Write g.γd g.f g.R qc (encImg I) Hf hlen) $$ Hdur Hos Hsh Hdi Hdh Hcp
    iapply DurFs.durAupd_wand_post
    isplitl [HAU]
    · iapply HAU; ipureintro; exact hlen
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iintro %_ H
    iapply dk_writeSync_wand
    iframe H
    iintro H Hdh Hcp
    isplitr
    · ipureintro; trivial
    iapply H $$ Hdh Hcp
  iintro %v ⟨%Hv, HΦ⟩
  subst Hv
  try wp_auto
  iapply HΦ $$ Hmem

end sec

end Perennial
