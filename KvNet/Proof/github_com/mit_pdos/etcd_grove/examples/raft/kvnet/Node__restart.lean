/-
The proof of `KvNet/Spec/.../kvnet/Node__restart.lean` (2026-11-24, G5), generic in the store's
seams: under `Node.mu` (`nodeLockInv`: the current incarnation and its stopper), the node's
`stopLaw` turns the stopper into the start resource `R`, `Stats.add` counts, and its `startLaw`
turns `R` into the next incarnation (with its stopper), which the fields then hold.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__restart
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Stats__add

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

theorem Node.restart.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Node.restart.spec (GF := GF) (hG := hG) F rep stp := by
  intro nd γ N id
  wp_start as #Hnd
  iunfold isNodeS at Hnd
  icases Hnd with ⟨%cfg, %M, %sp, %f, #Hcfg, %Hid, #HM, #Hst, #Hstats, #HnewT, #Hstep, %Htr,
    ⟨%AP, %R, #Hctor, #Hstop, #Hstart⟩, #Hmu⟩
  subst Hid
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold nodeLockInv at HL
  icases HL with ⟨%r, %tv, %n, Hr, Ht, #Hrn, #Hrep, #Hn, Hstp⟩
  try wp_auto
  -- the incarnation stopped: the start resource back
  iunfold stopLaw at Hstop
  ihave Hstop1 := Hstop $$ %r %tv
  wp_apply Hstop1 $$ [$Hpkg $Hstp] as HR
  try wp_auto
  wp_apply wp_add sp (W64 23) (by decide) (by decide) $$ [$Hpkg $Hstats]
  try wp_auto
  -- the next one started from it
  iunfold startLaw at Hstart
  ihave Hstart1 := Hstart $$ %sp %f
  wp_apply Hstart1 $$ [$Hpkg $HM $HR $Hstats $Hctor] as %r' %tv' ⟨%n', #Hrn', #Hrep', #Hn', Hstp'⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hr Ht Hstp']
  · inext
    iunfold nodeLockInv
    iexists r', tv', n'
    iframe
  try wp_auto
  iapply HΦ
  itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
