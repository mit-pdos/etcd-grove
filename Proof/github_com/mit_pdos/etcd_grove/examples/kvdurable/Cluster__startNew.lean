/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__startNew.lean`. Lean-first
(no Rocq counterpart).

kvreconf's, with the replica started by `Cluster.start`: under `c.mu`, with fewer than `maxReplicas`
replicas (the map's keys are `1 … nextID-1`, so `nextID ≤ 9`), the fresh id `nextID` is joined
(`joinAuth_join`: its durable state at `RaftState.init` and its vacant id), its file's invariant
allocated at no contents from the lock's fresh entries (`kdFile_alloc`: the writer's half for
`start`), the next-id bound raised (`repKnown`), and the incarnation `start` returns put in the map.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__startNew
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__start
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.StartLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClusterLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem Cluster.startNew.wp_proof
    (wp_start : Cluster.start.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Cluster.startNew.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c
  wp_start as #Hc
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold clusterLockInv at HL
  iNamed HL
  obtain ⟨HdomR, HdomU, Hvn, Hn10⟩ := Hdom
  have Hsz : GMap.size R = uint.nat nid - 1 :=
    kvreconf.size_of_keys R (uint.nat nid) Hn10 (by omega) HdomR
  try wp_auto
  wp_apply wp_map_len_lt mR R _ $$ [$HR] as ⟨HR, %Hlt⟩
  wp_if_destruct
  · -- `maxReplicas` started: nothing changes
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hreps Hfiles]
    · inext
      unfold clusterLockInv
      iexists mR, R, nid, nop, U
      iframe
      ipureintro; exact ⟨HdomR, HdomU, Hvn, Hn10⟩
    try wp_auto
    iapply HΦ; iintro %h; cases h
  have Hn9 : uint.nat nid < 10 := by word
  have Hnid0 : nid ≠ W64 0 := by intro h; rw [h] at Hvn; simp at Hvn
  try wp_auto
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨#Hic, -, -, -, -, -⟩
  have HnU : nid ∉ U := by rw [HdomU]; omega
  imod joinAuth_join γ.r.cluster kdRaftN U nid HnU Hnid0 $$ [$Hic $Hjoin] with ⟨Hjoin, HrS, Hvac⟩
  -- the id's file: its invariant at no contents, the writer's half for `start`
  have e2 : uint.nat (nid + W64 1) = uint.nat nid + 1 := by word
  have Hfr : kvreconf.freshIds (uint.nat nid) = nid :: kvreconf.freshIds (uint.nat (nid + W64 1)) := by
    rw [kvreconf.freshIds_cons _ Hn9, e2]; congr 1; word
  rw [Hfr]
  icases Hfiles with ⟨⟨Hdf, %g, Hg⟩, Hfiles⟩
  imod kdFile_alloc γ dir nid ⊤ g $$ Hdf Hg HrS with ⟨#HfInv, Hwr⟩
  -- the new id is known: the next-id bound raised
  imod mono_nat_own_update (uint.nat nid + 1) (by omega) $$ HnidA with ⟨HnidA, #Hlb⟩
  ihave #Hknown : repKnown γ nid $$ []
  · unfold repKnown; iframe Hlb; ipureintro; exact Hnid0
  wp_apply wp_start γ vs dir c nid RaftState.init none (by word) (by word)
    $$ [$Hc $HfInv $Hvac $Hwr $Hknown] as %r ⟨Hr, -⟩
  have HRn : R !! nid = none := by
    cases h : R !! nid with
    | none => rfl
    | some _ => have := (HdomR nid).1 (by simp [h]); omega
  wp_apply wp_mapInsert go.uint64 mR R nid r $$ [$HR] as HR
  try wp_auto
  ihave #Hctr := isStats_field (c.[KCluster, go!"Stats"]) go!"ReplicasStarted" (by decide) $$ Hstats
  wp_apply wp_add (c.[KCluster, go!"Stats"]) _ $$ [$Hpkg $Hctr]
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hreps Hr
      Hfiles]
  · inext
    unfold clusterLockInv
    iexists mR, <[nid := r]> R, nid + W64 1, nop, {nid} ∪ U
    rw [e2]
    iframe Hnid Hnop Hopn HnidA Hjoin HmR HR Hfiles
    isplitr
    · ipureintro
      refine ⟨?_, ?_, by omega, by omega⟩
      · intro i
        by_cases hi : nid = i
        · subst hi; simp; omega
        · rw [GMap.lookup_insert_ne _ _ hi, HdomR]
          have : uint.nat i ≠ uint.nat nid := fun h => hi (by word)
          omega
      · intro i
        rw [GMap.elem_of_union, GMap.elem_of_singleton, HdomU]
        constructor
        · rintro (rfl | h) <;> omega
        · intro h
          by_cases hi : i = nid
          · left; exact hi
          · right; have : uint.nat i ≠ uint.nat nid := fun h => hi (by word)
            omega
    iapply (BigSepM.bigSepM_insert (Φ := fun id r => isRep (GF := GF) γ vs dir id r) HRn).2
    iframe Hreps
    unfold isRep
    iexact Hr
  try wp_auto
  iapply HΦ
  iintro -
  iexact Hknown

end proof

end kvdurable
end EtcdGrove
end Perennial
