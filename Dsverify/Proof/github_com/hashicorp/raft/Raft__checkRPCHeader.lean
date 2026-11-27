/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__checkRPCHeader.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).checkRPCHeader`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__checkRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.AppendEntriesRequest__GetRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.RequestVoteRequest__GetRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.RequestPreVoteRequest__GetRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.TimeoutNowRequest__GetRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.InstallSnapshotRequest__GetRPCHeader

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.Raft.checkRPCHeader.wp_proof
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_ae_hdr : github_com.hashicorp.raft.AppendEntriesRequest.GetRPCHeader.spec (GF := GF) (hG := hG))
    (wp_rv_hdr : github_com.hashicorp.raft.RequestVoteRequest.GetRPCHeader.spec (GF := GF) (hG := hG))
    (wp_pv_hdr : github_com.hashicorp.raft.RequestPreVoteRequest.GetRPCHeader.spec (GF := GF) (hG := hG))
    (wp_tn_hdr : github_com.hashicorp.raft.TimeoutNowRequest.GetRPCHeader.spec (GF := GF) (hG := hG))
    (wp_is_hdr : github_com.hashicorp.raft.InstallSnapshotRequest.GetRPCHeader.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.checkRPCHeader.spec (GF := GF) (hG := hG) :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r γ rc i rpc p rq
    wp_start as ⟨#Hr, ⟨%Hc, %Hv⟩, Hp⟩
    have Hts : go.typeSetContains (go.GoType.PointerType AppendEntriesRequest.ty) WithRPCHeader.ty = true := by
      go_type_set
    wp_auto
    rw [Hc]
    wp_auto
    simp only [Hts, ite_true]
    wp_auto
    wp_apply wp_ae_hdr p rq $$ [$Hp] as Hp
    rw [Hv]
    wp_auto
    rw [Hv]
    wp_auto
    wp_apply wp_config r γ rc i $$ [$Hr] as %c1 %Hc1
    rw [Hc1.1, Hv]
    wp_auto
    wp_end
  · intro r γ rc i rpc p rq
    wp_start as ⟨#Hr, ⟨%Hc, %Hv⟩, Hp⟩
    have Hts : go.typeSetContains (go.GoType.PointerType RequestVoteRequest.ty) WithRPCHeader.ty = true := by
      go_type_set
    wp_auto
    rw [Hc]
    wp_auto
    simp only [Hts, ite_true]
    wp_auto
    wp_apply wp_rv_hdr p rq $$ [$Hp] as Hp
    rw [Hv]
    wp_auto
    rw [Hv]
    wp_auto
    wp_apply wp_config r γ rc i $$ [$Hr] as %c1 %Hc1
    rw [Hc1.1, Hv]
    wp_auto
    wp_end
  · intro r γ rc i rpc p rq
    wp_start as ⟨#Hr, ⟨%Hc, %Hv⟩, Hp⟩
    have Hts : go.typeSetContains (go.GoType.PointerType RequestPreVoteRequest.ty) WithRPCHeader.ty = true := by
      go_type_set
    wp_auto
    rw [Hc]
    wp_auto
    simp only [Hts, ite_true]
    wp_auto
    wp_apply wp_pv_hdr p rq $$ [$Hp] as Hp
    rw [Hv]
    wp_auto
    rw [Hv]
    wp_auto
    wp_apply wp_config r γ rc i $$ [$Hr] as %c1 %Hc1
    rw [Hc1.1, Hv]
    wp_auto
    wp_end
  · intro r γ rc i rpc p rq
    wp_start as ⟨#Hr, ⟨%Hc, %Hv⟩, Hp⟩
    have Hts : go.typeSetContains (go.GoType.PointerType TimeoutNowRequest.ty) WithRPCHeader.ty = true := by
      go_type_set
    wp_auto
    rw [Hc]
    wp_auto
    simp only [Hts, ite_true]
    wp_auto
    wp_apply wp_tn_hdr p rq $$ [$Hp] as Hp
    rw [Hv]
    wp_auto
    rw [Hv]
    wp_auto
    wp_apply wp_config r γ rc i $$ [$Hr] as %c1 %Hc1
    rw [Hc1.1, Hv]
    wp_auto
    wp_end
  · intro r γ rc i rpc p rq
    wp_start as ⟨#Hr, ⟨%Hc, %Hv⟩, Hp⟩
    have Hts : go.typeSetContains (go.GoType.PointerType InstallSnapshotRequest.ty) WithRPCHeader.ty = true := by
      go_type_set
    wp_auto
    rw [Hc]
    wp_auto
    simp only [Hts, ite_true]
    wp_auto
    wp_apply wp_is_hdr p rq $$ [$Hp] as Hp
    rw [Hv]
    wp_auto
    rw [Hv]
    wp_auto
    wp_apply wp_config r γ rc i $$ [$Hr] as %c1 %Hc1
    rw [Hc1.1, Hv]
    wp_auto
    wp_end
