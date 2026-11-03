/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__restart.lean`. Lean-first
(no Rocq counterpart).

`c.replica(id)` at its pinned spec trades the crasher's token for the current incarnation `r`
(`curRep`, `repStop`), whose persistent part gives the id's file invariant and bounds; `crash` gives
back the vacant slot and the writer's half, which `Cluster.start` takes to start the next incarnation
`r'`. Under `c.mu`: the fragment says `c.replicas[id]` is still `r` and the id's entry holds the
token (a second fragment would be a second full one); `r'` is made current (the map, the ghost map,
`isRep`), its fragment and `repStop` go in the entry, and the token comes out.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__restart
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__replica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__crash
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__start
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws

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

/-- The persistent facts of an incarnation `repStop` holds: its file's invariant and its id's bounds. -/
theorem repStop_info (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) :
    repStop (GF := GF) γ vs dir id r ⊢
      repStop γ vs dir id r ∗ kdFileInv γ dir id ∗ ⌜1 ≤ uint.nat id ∧ uint.nat id ≤ 9⌝ := by
  iintro H
  ihave #Hp : iprop(kdFileInv γ dir id ∗ ⌜1 ≤ uint.nat id ∧ uint.nat id ≤ 9⌝) $$ [H]
  · iunfold repStop at H
    icases H with ⟨H, -⟩
    iunfold repStopper at H
    icases H with ⟨%n, %st, %sts, %sq, %ρ, #HR, -⟩
    iunfold isReplicaR at HR
    icases HR with ⟨#Hrep, -⟩
    iunfold isReplica at Hrep
    icases Hrep with ⟨-, %Hidr, -, -, -, -, -, -, -, -, -, -, #HfInv, -⟩
    iframe HfInv
    ipureintro; exact Hidr
  iframe H Hp

theorem Cluster.restart.wp_proof
    (wp_replicaPin : Cluster.replica.specPin (GF := GF) (hG := hG))
    (wp_crash : Replica.crash.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_start : Cluster.start.spec (GF := GF) (hG := hG)) :
    Cluster.restart.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c id
  wp_start as ⟨#Hc, #Hknown, Hcr⟩
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  wp_auto
  wp_apply wp_replicaPin γ vs dir c id $$ [$Hc $Hknown $Hcr] as %r ⟨Hfrag, Hstop⟩
  icases repStop_info γ vs dir id r $$ Hstop with ⟨Hstop, #HfInv, %Hidr⟩
  try wp_auto
  wp_apply wp_crash γ vs dir id r $$ [$Hstop] as ⟨Hvac, %S, %o, Hwr⟩
  try wp_auto
  ihave #Hctr := isStats_field (c.[KCluster, go!"Stats"]) go!"Crashes" (by decide) $$ Hstats
  wp_apply wp_add (c.[KCluster, go!"Stats"]) _ $$ [$Hpkg $Hctr]
  try wp_auto
  wp_apply wp_start γ vs dir c id S o Hidr.1 Hidr.2 $$ [$Hc $HfInv $Hvac $Hwr $Hknown]
    as %r' ⟨Hr', Hstop'⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold clusterLockInv at HL
  iNamed HL
  iunfold curRep at Hfrag
  ihave %HRid := ghost_map_lookup $$ Hcur Hfrag
  -- (2026-11-01, the stopper) not stopped: the stopped lock holds every fragment, ours among them
  icases Hstops with (⟨-, Hfrs⟩ | Hstops)
  · ihave Hfrag2 := BigSepM.bigSepM_lookup_acc (Φ := fun id r => curRep (GF := GF) γ id r) HRid $$ Hfrs
    icases Hfrag2 with ⟨Hfrag2, -⟩
    iunfold curRep at Hfrag2
    ihave %Hne := ghostMapElem_ne γ.cur id id (DFrac.own 1) r r $$ Hfrag Hfrag2
    exact absurd rfl Hne
  icases (BigSepM.bigSepM_delete
    (Φ := fun id r => iprop((curRep (GF := GF) γ id r ∗ repStop γ vs dir id r) ∨ crasher γ))
    (m := R) HRid).1 $$ Hstops with ⟨Hst, Hstops⟩
  icases Hst with (⟨Hfrag2, -⟩ | Hcr)
  · iunfold curRep at Hfrag2
    ihave %Hne := ghostMapElem_ne γ.cur id id (DFrac.own 1) r r $$ Hfrag Hfrag2
    exact absurd rfl Hne
  try wp_auto
  wp_apply wp_mapInsert go.uint64 mR R id r' $$ [$HR] as HR
  imod ghost_map_update r' $$ Hcur Hfrag with ⟨Hcur, Hfrag⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hreps Hr'
      Hcur Hstops Hstop' Hfrag Hfiles]
  · inext
    unfold clusterLockInv
    iexists mR, <[id := r']> R, nid, nop, U
    iframe HmR HR Hnid Hnop Hopn HnidA Hjoin Hcur Hfiles
    isplitr
    · ipureintro
      obtain ⟨HdomR, HdomU, Hvn, Hn10⟩ := Hdom
      refine ⟨fun i => ?_, HdomU, Hvn, Hn10⟩
      by_cases hi : id = i
      · subst hi; rw [← HdomR, HRid]; simp
      · rw [GMap.lookup_insert_ne _ _ hi, HdomR]
    isplitl [Hreps Hr']
    · iapply BigSepM.bigSepM_insert_elim (Φ := fun id r => isRep (GF := GF) γ vs dir id r) $$ [Hr']
        Hreps
      unfold isRep
      iexact Hr'
    iright
    iapply (BigSepM.bigSepM_insert_delete
      (Φ := fun id r => iprop((curRep (GF := GF) γ id r ∗ repStop γ vs dir id r) ∨ crasher γ))).2
    iframe Hstops
    ileft
    unfold curRep
    iframe Hfrag Hstop'
  try wp_auto
  iapply HΦ
  iexact Hcr

end proof

end kvdurable
end EtcdGrove
end Perennial
