/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__Read.lean`. Lean-first (no
Rocq counterpart): a read at a random member (`Replica.read`, from the client's lower bound `L0`),
retried until one answers; a read has no effect, so each attempt is a fresh one.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__Read
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__randomMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__read
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Cluster.Read.wp_proof
    (wp_randomMember : Cluster.randomMember.spec (GF := GF) (hG := hG))
    (wp_read : Replica.read.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Cluster.Read.spec (GF := GF) (hG := hG) := by
  intro γr vs c key L0 Hkey
  wp_start as ⟨#Hcc, #HL0⟩
  ihave #Hcc' := Hcc
  iunfold isClusterC at Hcc'
  iNamed Hcc'
  try wp_auto
  ihave HI : iprop(True) $$ []
  · itrivial
  wp_for HI
  wp_apply wp_randomMember γr vs c $$ [$Hcc] as %r ⟨%rid, #Hr⟩
  wp_apply wp_read γr vs rid r key (W64 100000000) L0 Hkey $$ [$Hr $HL0] as %v %ok Hres
  try wp_auto
  cases ok
  · -- no answer: another attempt
    simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    ihave #Hctr := isStats_field (c.[RCluster, go!"Stats"]) go!"Retries" (by decide) $$ Hstats
    wp_apply wp_add _ _ $$ [$Hpkg $Hctr]
    wp_for_post
    iframe
  · simp only [↓reduceIte]
    try wp_auto
    wp_for_post
    iapply HΦ $$ Hres

end proof

end kvreconf
end EtcdGrove
end Perennial
