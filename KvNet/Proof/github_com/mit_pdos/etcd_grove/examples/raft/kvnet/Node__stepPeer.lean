/-
The proof of `KvNet/Spec/.../kvnet/Node__stepPeer.lean` (2026-11-24, G5; the step part of the
former `Transport.servePeer`): count, read the current incarnation's replica (`Node.current`), and step
the message on its node (`stepLaw`, `node.Step`) under a timeout.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__stepPeer
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__current
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.withTimeout
public import KvNet.Spec.go_etcd_io.raft.v3.node__Step

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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Node.stepPeer.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (wp_current : Node.current.spec (GF := GF) (hG := hG) F rep stp)
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_withTimeout : withTimeout.spec (GF := GF) (hG := hG))
    (wp_Step : node.Step.spec (GF := GF) (hG := hG)) :
    Node.stepPeer.spec (GF := GF) (hG := hG) F rep stp := by
  intro nd γ N id ml src st HTo
  wp_start as ⟨#Hnd, #Hcc, #Hmsg, Hm⟩
  ihave #Hnd' := Hnd
  iunfold isNodeS at Hnd'
  icases Hnd' with ⟨%cfg, %M, %sp, %f, #Hcfg, %Hid, #HM, #Hst, #Hstats, #HnewT, #Hstep, %Htr, -, #Hmu⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_add sp (W64 18) (by decide) (by decide) $$ [$Hpkg $Hstats]
  try wp_auto
  wp_apply wp_current nd γ N id $$ [$Hpkg $Hnd] as %r ⟨%n, #Hrn, #Hrep, #Hn⟩
  try wp_auto
  wp_apply wp_withTimeout _ $$ [$Hpkg $Hcc] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx, -⟩
  try wp_auto
  ihave #Hnc : nodeCtx ctx' cd $$ []
  · unfold nodeCtx; iright; iexact Hctx
  iunfold stepLaw at Hstep
  imod Hstep $$ %src %st %ml %HTo Hmsg Hm with Hin
  wp_apply wp_Step n γ N _ ml ctx' cd $$ [$Hraft $Hn $Hnc $Hin] as %err -
  try wp_auto
  wp_apply Hcancel
  try wp_auto
  iapply HΦ
  itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
