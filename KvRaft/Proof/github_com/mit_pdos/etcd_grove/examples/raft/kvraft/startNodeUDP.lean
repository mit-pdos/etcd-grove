/-
The proof of `KvRaft/Spec/.../kvraft/startNodeUDP.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`), at
the store's seam as `StartNode.wp_proof` (`kvFacts γ`, `kvRep γ vs dir`, `kvConfRead`, `kvStp γ vs dir`,
the start resource `kvNodeStart γ vs dir`): `openUDP`, then `startNode` with `u.newTransport` as the
constructor. `udpNet.newTransport.spec` gives `ptCtor` at any per-address premise, so at TCP's `tcpAP`,
where the kvraft lead's `start.spec` instance (`start.wp_proof`, at `tcpAP`, `kvStp`, `kvNodeStart`) is: the
UDP side reuses `start`, `stopIncarnation`, `kv_stepLaw` and `kv_confLaw` unchanged (as `StartNode`'s
proof uses them).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.startNodeUDP
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.openUDP
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet__newTransport
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.startNode
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.start
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.stopIncarnation
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.StartDefs
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.ConfLaw
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.SendLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions]
variable [go.IntoValInj GoString] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem startNodeUDP.wp_proof (γ : KdNames) (vs : List w64) (dir : GoString)
    (wp_openUDP : openUDP.spec (GF := GF) (hG := hG))
    (wp_newTransport : udpNet.newTransport.spec (GF := GF) (hG := hG))
    (wp_startNode : startNode.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True)) (kvRep γ vs dir)
      (kvStp γ vs dir))
    (wp_start : start.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True))
      (tcpAP (kvFacts γ (fun _ => True))) (kvRep γ vs dir) (kvStp γ vs dir) (kvNodeStart γ vs dir)
      γ.r.cluster kdRaftN)
    (wp_stopIncarnation : stopIncarnation.spec (GF := GF) (hG := hG) (kvStp γ vs dir)
      (kvNodeStart γ vs dir)) :
    startNodeUDP.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True)) (kvRep γ vs dir) kvConfRead
      (kvStp γ vs dir) (kvNodeStart γ vs dir) := by
  intro γu cfg M a Hma Hok
  wp_start as ⟨#HM, HS, Hu⟩
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
  try wp_auto
  wp_apply wp_openUDP (kvFacts γ (fun _ => True)) γu cfg M a Hma Hok $$ [$Hpkg $HM $Hu]
    as %u ⟨%boot, #Hun⟩
  -- the transport constructor: the endpoint's method value, at TCP's per-address premise
  ihave #Hctor : ptCtor (kvFacts γ (fun _ => True)) γ.r.cluster kdRaftN cfg.ID'
      (tcpAP (kvFacts γ (fun _ => True)))
      (methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet.ty)
        go!"newTransport" #u) $$ []
  · unfold ptCtor
    iintro !> %am %M' %sts %Φ' !> ⟨Hpkg', #HM', #Hsts, -⟩ HΦ'
    iapply wp_newTransport (kvFacts γ (fun _ => True)) γu u cfg.ID' boot γ.r.cluster kdRaftN am M' sts
      Htr0 $$ [$Hpkg' $Hun $HM' $Hsts]
    iexact HΦ'
  ihave #Hstep := kv_stepLaw (GF := GF) γ (fun _ => True) cfg.ID' Htr0 Hmd (by rw [Hsl])
  ihave #Hstop := wp_stopIncarnation cfg M
  ihave #Hstart := wp_start cfg M
  try wp_auto
  wp_apply wp_startNode cfg M
      (methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpNet.ty)
        go!"newTransport" #u)
      γ.r.cluster kdRaftN (tcpAP (kvFacts γ (fun _ => True))) (kvNodeStart γ vs dir cfg.ID' cfg.Dir' cfg.Opts' M)
    $$ [$Hpkg $HM $HS $Hctor $Hstep $Hstop $Hstart] as %nd #Hnd
  · ipureintro; exact Htr0
  subst Hdir
  ihave #Hlaw := kv_confLaw (GF := GF) γ vs cfg.Dir' cfg.ID'
  try wp_auto
  iapply HΦ
  iexists γ.r.cluster, kdRaftN, boot
  iframe Hnd Hlaw Hun

end proof

end kvraft
end EtcdGrove
end Perennial
