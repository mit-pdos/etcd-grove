/-
Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/StartNode.lean` (2026-11-24, G5:
`startNode` with TCP's transport), at the store's seam (`kvFacts γ`, `kvRep γ vs dir`, `kvConfRead`, the
stopper `kvStp γ vs dir`) and the start resource `kvNodeStart γ vs dir` (`StartDefs.lean`): `startNode`
with `newTCPTransport` as the constructor (`ptCtor` at `tcpAP`, from its spec at the untraced cluster),
the step law (`kv_stepLaw`), the restart's laws (`start.spec`, `stopIncarnation.spec`), and the
conf law (`kv_confLaw`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.StartNode
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.startNode
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.newTCPTransport
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.start
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.stopIncarnation
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.StartDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.ConfLaw
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.SendLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [go.IntoValInj GoString] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem StartNode.wp_proof (γ : KdNames) (vs : List w64) (dir : GoString)
    (wp_startNode : startNode.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True)) (kvRep γ vs dir)
      (kvStp γ vs dir))
    (wp_newTCPTransport : newTCPTransport.spec (GF := GF) (hG := hG))
    (wp_start : start.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True))
      (tcpAP (kvFacts γ (fun _ => True))) (kvRep γ vs dir) (kvStp γ vs dir) (kvNodeStart γ vs dir)
      γ.r.cluster kdRaftN)
    (wp_stopIncarnation : stopIncarnation.spec (GF := GF) (hG := hG) (kvStp γ vs dir)
      (kvNodeStart γ vs dir)) :
    StartNode.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True)) (kvRep γ vs dir) kvConfRead
      (kvStp γ vs dir) (kvNodeStart γ vs dir) := by
  intro cfg M
  wp_start as ⟨#HM, HS⟩
  -- the cluster's facts, read off the start resource (which goes on whole)
  iunfold kvNodeStart at HS
  icases HS with ⟨%Hdir, %fl, %qc, Hst, #Hglob, #Hpeers, %Hopts⟩
  ihave #Hglob' := Hglob
  iunfold kvStartGlobals at Hglob'
  icases Hglob' with ⟨%Hcf, -⟩
  obtain ⟨Hdup, Hbl0, Htr0, Hsl, Hmd, Hmax⟩ := Hcf
  ihave HS : kvNodeStart γ vs dir cfg.ID' cfg.Dir' cfg.Opts' M $$ [Hst]
  · iunfold kvNodeStart
    isplitr
    · ipureintro; exact Hdir
    iexists fl, qc
    iframe Hst Hglob Hpeers
    ipureintro; exact Hopts
  -- the transport constructor, the step law and the restart's laws
  ihave #Hctor : ptCtor (kvFacts γ (fun _ => True)) γ.r.cluster kdRaftN cfg.ID'
      (tcpAP (kvFacts γ (fun _ => True)))
      (functions github_com.mit_pdos.etcd_grove.examples.raft.kvnet.newTCPTransport []) $$ []
  · unfold ptCtor
    simp only [tcpAP]
    iintro !> %am %M' %sts %Φ' !> ⟨Hpkg', #HM', #Hsts, #Hap⟩ HΦ'
    iapply wp_newTCPTransport (kvFacts γ (fun _ => True)) γ.r.cluster kdRaftN cfg.ID' am M' sts Htr0
      $$ [$Hpkg' $HM' $Hsts $Hap]
    iexact HΦ'
  ihave #Hstep := kv_stepLaw (GF := GF) γ (fun _ => True) cfg.ID' Htr0 Hmd (by rw [Hsl])
  ihave #Hstop := wp_stopIncarnation cfg M
  ihave #Hstart := wp_start cfg M
  try wp_auto
  wp_apply wp_startNode cfg M (functions github_com.mit_pdos.etcd_grove.examples.raft.kvnet.newTCPTransport [])
      γ.r.cluster kdRaftN (tcpAP (kvFacts γ (fun _ => True))) (kvNodeStart γ vs dir cfg.ID' cfg.Dir' cfg.Opts' M)
    $$ [$Hpkg $HM $HS $Hctor $Hstep $Hstop $Hstart] as %nd #Hnd
  · ipureintro; exact Htr0
  subst Hdir
  ihave #Hlaw := kv_confLaw (GF := GF) γ vs cfg.Dir' cfg.ID'
  iapply HΦ
  iexists γ.r.cluster, kdRaftN
  iframe Hnd Hlaw

end proof

end raft_kvnet
end EtcdGrove
end Perennial
