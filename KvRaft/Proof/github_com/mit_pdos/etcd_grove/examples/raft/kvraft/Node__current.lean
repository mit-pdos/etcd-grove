/-
The proof of `KvRaft/Spec/.../kvraft/Node__current.lean` (2026-11-24, G5): read the current
incarnation's replica under `Node.mu` (`nodeLockInv`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__current

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Node.current.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) :
    Node.current.spec (GF := GF) (hG := hG) F rep stp := by
  intro nd γ N id
  wp_start as #Hnd
  iunfold isNodeS at Hnd
  icases Hnd with ⟨%cfg, %M, %sp, %f, #Hcfg, %Hid, #HM, #Hst, #Hstats, #HnewT, #Hstep, %Htr, -, #Hmu⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold nodeLockInv at HL
  icases HL with ⟨%r, %tv, %n, Hr, Ht, #Hrn, #Hrep, #Hn, Hstp⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hr Ht Hstp]
  · inext
    iunfold nodeLockInv
    iexists r, tv, n
    iframe Hr Ht Hstp
    isplitr
    · iexact Hrn
    isplitr
    · imodintro; iexact Hrep
    iexact Hn
  iapply HΦ
  iexists n
  isplitr
  · iexact Hrn
  isplitr
  · imodintro; iexact Hrep
  iexact Hn

end proof

end kvraft
end EtcdGrove
end Perennial
