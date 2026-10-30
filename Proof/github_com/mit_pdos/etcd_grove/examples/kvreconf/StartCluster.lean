/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/StartCluster.lean`. Lean-first
(no Rocq counterpart).

The ghost state first: raft's cluster of the voters `vs = bootVoters Voters` (`cluster_alloc`,
`dup = true`), its decisions handed to the store's rule (`confPolicy_alloc`), the next-id bound at
`Voters+1`, the stopper's flag, the store's invariant (`rkvInv_alloc`: every id's read sequence at
`0`) and the snapshot registry. Then the cluster's struct: the bootstrap `ConfState` (the voters
appended, frozen read-only), the `Stats` counters (`isStats_alloc`), `c.mu` locked fresh
(`wp_Mutex_Lock_fresh`: its invariant is due at the `Unlock`). The loop starts each founder as
`startNew` starts a newcomer, with its `nodeFounder` token; the `Unlock` gives the lock its
invariant: the founders' replicas and stop tokens, the ids above them fresh.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.StartCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.MutexFresh
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__config
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__tick
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__sender
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.newReplica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClusterLemmas

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

theorem StartCluster.wp_proof
    (wp_config : Cluster.config.spec (GF := GF) (hG := hG))
    (wp_tick : Cluster.tick.spec (GF := GF) (hG := hG))
    (wp_sender : Cluster.sender.spec (GF := GF) (hG := hG))
    (wp_newReplica : newReplica.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_RestartNode : RestartNode.spec (GF := GF) (hG := hG))
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG))
    (wp_InitialState : Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG)) :
    StartCluster.spec (GF := GF) (hG := hG) := by
  intro o Hok Hrb
  wp_start as ⟨#Hcci, #HstorInv⟩
  obtain ⟨HV1, HV5, Hm1, Hm2, Hsz⟩ := Hok
  have HVn : uint.nat o.Voters' ≤ 5 := by word
  have HV0 : 1 ≤ uint.nat o.Voters' := by word
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  -- the ghost state
  imod cluster_alloc (GF := GF) kvrRaftN (bootVoters (uint.nat o.Voters')) true ⊤ Hrb
    (by intro h; have := congrArg List.length h; rw [bootVoters_length] at this; simp at this; omega)
    (bootVoters_nodup _ (by omega)) (bootVoters_zero _ (by omega))
    (by rw [bootVoters_length]; omega)
    with ⟨%γ, %Hdup, Hops, HU, #Hiscl, Hdec, #Hca0, Hsm, Hjoin, Hfounders⟩
  imod confPolicy_alloc γ kvrConfN kvrRule ⊤ $$ Hdec with #Hpol
  imod mono_nat_own_alloc (GF := GF) (uint.nat o.Voters' + 1) with ⟨%γn, HnidA, #Hlb⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γs, Hstp⟩
  icases (ghostVar_split_half (GF := GF) γs 1 false).1 $$ Hstp with ⟨Hstp1, Hstp2⟩
  imod rkvInv_alloc ⊤ γ γn γs $$ Hops HU with ⟨%γr, %Hγr, #Hinv, Hval, Hopn, Hrseqs⟩
  obtain ⟨Hγc, Hγn, Hγs⟩ := Hγr
  subst Hγc Hγn Hγs
  imod kvrSnapInv_alloc γr ⊤ $$ Hsm with #Hsinv
  ihave #Hcl : kvrCluster γr (bootVoters (uint.nat o.Voters')) $$ []
  · unfold kvrCluster; iframe #
  try wp_auto
  icases typedPointsto_split _ _ _ $$ opts with Hopt
  simp only [TypedPointsto.typedPointstoDef]
  icases Hopt with ⟨Hov, -⟩
  try wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mR HR
  try wp_auto
  icases typedPointsto_split _ _ _ $$ «$r0» with Hc0
  simp only [TypedPointsto.typedPointstoDef]
  icases Hc0 with ⟨opts, Stats, boot, mu, replicas, nextID, nextOp, -⟩
  ipersist opts
  ipersist boot
  ihave #Hos := opts
  icases typedPointsto_split _ _ _ $$ Hos with Hos
  simp only [TypedPointsto.typedPointstoDef]
  icases Hos with ⟨#oV, #oP, #oC, #oS, #oM, #oMC, #oI, -⟩
  ihave %Hv3nn := typedPointsto_not_null $$ «$v3»
  icases typedPointsto_split _ _ _ $$ «$v3» with Hv3
  simp only [TypedPointsto.typedPointstoDef]
  icases Hv3 with ⟨state, Voters, Learners, VotersOutgoing, LearnersNext, AutoLeave, unknownFields,
    sizeCache, -⟩
  -- the bootstrap voters
  ihave IH : iprop(∃ (k : w64) (sv : GoSlice),
      "id" ∷ id_ptr ↦ k ∗ "HbV" ∷ «$v3_ptr».[raftpb.ConfState, go!"Voters"] ↦ sv ∗
      "Hsv" ∷ sv ↦* bootVoters (uint.nat k - 1) ∗ "Hsvc" ∷ ownSliceCap w64 sv (DFrac.own 1) ∗
      "%Hk" ∷ ⌜1 ≤ uint.nat k ∧ uint.nat k ≤ uint.nat o.Voters' + 1⌝) $$ [id Voters]
  · iexists W64 1, slice.nil
    iframe id Voters
    simp only [named, show uint.nat (W64 1) - 1 = 0 from rfl, show bootVoters 0 = [] from rfl]
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · try wp_auto
    wp_apply wp_slice_literal (V := w64) [k]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hsv $Hsvc $Hsl1] as %sv' ⟨Hsv, Hsvc, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, sv'
    have Hk1 : uint.nat (k + W64 1) - 1 = uint.nat k := by word
    have Hkv : uint.nat k ≤ uint.nat o.Voters' := by word
    have Hbv : bootVoters (uint.nat k - 1) ++ [k] = bootVoters (uint.nat k) := by
      obtain ⟨m, hm⟩ : ∃ m, uint.nat k = m + 1 := ⟨uint.nat k - 1, by omega⟩
      rw [hm, show m + 1 - 1 = m from by omega]
      simp only [bootVoters, List.range_succ, List.map_append, List.map_singleton]
      congr 2; word
    rw [Hk1, ← Hbv]
    iframe
    ipureintro; constructor <;> word
  have Hkv : uint.nat k = uint.nat o.Voters' + 1 := by word
  rw [Hkv, show uint.nat o.Voters' + 1 - 1 = uint.nat o.Voters' from by omega]
  try wp_auto
  sorry

end proof

end kvreconf
end EtcdGrove
end Perennial
