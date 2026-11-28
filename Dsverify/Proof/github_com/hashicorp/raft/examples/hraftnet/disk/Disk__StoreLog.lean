/-
(hraft_robust R3) The proof of `disk.(*Disk).StoreLog`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__StoreLog
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__StoreLogs

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

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StoreLog.wp_proof
    (wp_StoreLogs : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StoreLogs.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StoreLog.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf p first e
  iintro %Φ %Hpre #Hdisk #Hlp Hw HAU
  wp_method_call
  wp_call
  try wp_auto
  wp_apply (wp_slice_literal (V := Loc))
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  try wp_auto
  wp_bind (App (Val #(methods (go.GoType.PointerType Disk.ty) go!"StoreLogs" #d)) (Val _))
  iapply (wp_StoreLogs g d Wl Ws Wf _ (DFrac.own 1) [p] first [e]) $$ [] Hdisk Hsl [] Hw
  · ipureintro; refine ⟨Hpre.1, rfl, ?_⟩; have := Hpre.2; simp only [List.length_singleton]; omega
  · iapply BigSepL.bigSepL_cons.2
    isplitl
    · iexists e; iframe #; ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2; itrivial
  iintro Hw' Hnc
  imod HAU $$ Hw' Hnc with ⟨Hnc, HAU⟩
  imodintro
  iframe Hnc
  inext
  icases HAU with ⟨%A, Hown, Hcl⟩
  iexists A
  iframe Hown
  iintro Hown
  imod Hcl $$ Hown with HΦ
  imodintro
  iintro _
  try wp_auto
  iexact HΦ

end sec

end Perennial
