/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/StartCluster.lean`. Lean-first
(no Rocq counterpart).

kvreconf's (its proof before durability stage I), with each voter started by `Cluster.start`. The
cluster's struct: the bootstrap `ConfState` (the voters appended, frozen read-only), the `readSeqs`
(its mutex at the read-sequence elements, all at `0`), the `Stats` counters (`isStats_alloc`), `c.mu`
locked fresh (`wp_Mutex_Lock_fresh`: its invariant is due at the `Unlock`). The next-id bound is
raised to `Voters+1` at once (each voter is then known). The loop starts each voter: its file's
invariant allocated at no contents (`kdFile_alloc`), `Cluster.start`, the incarnation put in the map
and made current (`γ.cur`); the `Unlock` gives the lock its invariant: the voters' incarnations and
`repStop`s, the ids above them fresh.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.StartCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__start
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.StartLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.MutexFresh
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.LifeLemmas
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

/-- A zero counter, in its invariant. -/
theorem kdCounter_alloc (l : Loc) (E : CoPset) :
    ⊢ (l ↦ (zero_val sync.atomic.Uint64) : IProp GF) ={E}=∗
      inv kdStatsN iprop(∃ v : w64, sync.atomic.ownUint64 l (DFrac.own 1) v) := by
  have hz : (l ↦ (zero_val sync.atomic.Uint64) : IProp GF) ⊢
      sync.atomic.ownUint64 l (DFrac.own 1) (W64 0) := by
    rw [sync.atomic.ownUint64_unseal]; unfold sync.atomic.ownUint64Def; exact .rfl
  iintro H
  iapply inv_alloc
  inext
  iexists W64 0
  iapply hz $$ H

/-- **A zero `Stats`**, its counters each in its invariant (kvreconf's `isStats_alloc`). -/
theorem isStats_alloc (st : Loc) (E : CoPset) :
    ⊢ (st ↦ (zero_val KStats) : IProp GF) ={E}=∗ isStats st := by
  iintro H
  icases typedPointsto_split _ _ _ $$ H with H
  simp only [TypedPointsto.typedPointstoDef]
  icases H with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, H17, H18,
    H19, H20, H21, H22, H23, -⟩
  imod kdCounter_alloc _ E $$ H1 with #H1
  imod kdCounter_alloc _ E $$ H2 with #H2
  imod kdCounter_alloc _ E $$ H3 with #H3
  imod kdCounter_alloc _ E $$ H4 with #H4
  imod kdCounter_alloc _ E $$ H5 with #H5
  imod kdCounter_alloc _ E $$ H6 with #H6
  imod kdCounter_alloc _ E $$ H7 with #H7
  imod kdCounter_alloc _ E $$ H8 with #H8
  imod kdCounter_alloc _ E $$ H9 with #H9
  imod kdCounter_alloc _ E $$ H10 with #H10
  imod kdCounter_alloc _ E $$ H11 with #H11
  imod kdCounter_alloc _ E $$ H12 with #H12
  imod kdCounter_alloc _ E $$ H13 with #H13
  imod kdCounter_alloc _ E $$ H14 with #H14
  imod kdCounter_alloc _ E $$ H15 with #H15
  imod kdCounter_alloc _ E $$ H16 with #H16
  imod kdCounter_alloc _ E $$ H17 with #H17
  imod kdCounter_alloc _ E $$ H18 with #H18
  imod kdCounter_alloc _ E $$ H19 with #H19
  imod kdCounter_alloc _ E $$ H20 with #H20
  imod kdCounter_alloc _ E $$ H21 with #H21
  imod kdCounter_alloc _ E $$ H22 with #H22
  imod kdCounter_alloc _ E $$ H23 with #H23
  imodintro
  unfold isStats
  simp only [statsFields]
  iframe #
  iapply (BigSepL.bigSepL_nil).2; iempintro

theorem StartCluster.wp_proof
    (wp_start : Cluster.start.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    StartCluster.spec (GF := GF) (hG := hG) := by
  intro γ o dir Hok
  dsimp only
  wp_start as ⟨#Hcci, #Hcl, #HstorInv, %Hdup, %Hbl0, #Hfits, Hvoters, Hjoin, Hfresh, Hopn, HnidA,
    Hrseqs, Hcur⟩
  obtain ⟨HV1, HV5, Hm1, Hm2, Hsz⟩ := Hok
  have HVn : uint.nat o.Voters' ≤ 5 := by word
  have HV0 : 1 ≤ uint.nat o.Voters' := by word
  try wp_auto
  icases typedPointsto_split _ _ _ $$ opts with Hopt
  simp only [TypedPointsto.typedPointstoDef]
  icases Hopt with ⟨Hov, -⟩
  try wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mR HR
  try wp_auto
  generalize hcl : «$r0_ptr» = cl
  icases typedPointsto_split _ _ _ $$ «$r0» with Hc0
  simp only [TypedPointsto.typedPointstoDef]
  icases Hc0 with ⟨opts, dirf, Stats, boot, seqs, mu, replicas, nextID, nextOp, -⟩
  ipersist opts
  ipersist dirf
  ipersist boot
  ipersist seqs
  ihave %Hv4nn := typedPointsto_not_null $$ «$v4»
  icases typedPointsto_split _ _ _ $$ «$v4» with Hv4
  simp only [TypedPointsto.typedPointstoDef]
  icases Hv4 with ⟨state, Voters, Learners, VotersOutgoing, LearnersNext, AutoLeave, unknownFields,
    sizeCache, -⟩
  icases typedPointsto_split _ _ _ $$ «$v5» with Hv5
  simp only [TypedPointsto.typedPointstoDef]
  icases Hv5 with ⟨smu, slast, -⟩
  -- the bootstrap voters
  ihave IH : iprop(∃ (k : w64) (sv : GoSlice),
      "id" ∷ id_ptr ↦ k ∗ "HbV" ∷ «$v4_ptr».[raftpb.ConfState, go!"Voters"] ↦ sv ∗
      "Hsv" ∷ sv ↦* kvreconf.bootVoters (uint.nat k - 1) ∗ "Hsvc" ∷ ownSliceCap w64 sv (DFrac.own 1) ∗
      "%Hk" ∷ ⌜1 ≤ uint.nat k ∧ uint.nat k ≤ uint.nat o.Voters' + 1⌝) $$ [id Voters]
  · iexists W64 1, slice.nil
    iframe id Voters
    simp only [named, show uint.nat (W64 1) - 1 = 0 from rfl, show kvreconf.bootVoters 0 = [] from rfl]
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
    have Hbv : kvreconf.bootVoters (uint.nat k - 1) ++ [k] = kvreconf.bootVoters (uint.nat k) := by
      obtain ⟨m, hm⟩ : ∃ m, uint.nat k = m + 1 := ⟨uint.nat k - 1, by omega⟩
      rw [hm, show m + 1 - 1 = m from by omega]
      simp only [kvreconf.bootVoters, List.range_succ, List.map_append, List.map_singleton]
      congr 2; word
    rw [Hk1, ← Hbv]
    iframe
    ipureintro; constructor <;> word
  have Hkv : uint.nat k = uint.nat o.Voters' + 1 := by word
  rw [Hkv, show uint.nat o.Voters' + 1 - 1 = uint.nat o.Voters' from by omega]
  try wp_auto
  -- the bootstrap conf state, frozen
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.ConfState «$v4_ptr» _ _ slice.nil [] ⊤ $$ [state sizeCache unknownFields Hnil]
    with #Hpb
  · iframe
  ihave HcsB : csPts «$v4_ptr» (DFrac.own 1) (kvreconf.bootCS (kvreconf.bootVoters (uint.nat o.Voters')))
    false $$ [HbV Hsv Learners VotersOutgoing LearnersNext AutoLeave]
  · iunfold csPts
    iexists sv, _, _, _, _
    simp only [named, kvreconf.bootCS]
    iframe HbV Hsv Learners VotersOutgoing LearnersNext AutoLeave Hpb
    isplitr
    · ipureintro; exact Hv4nn
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply cellRO_null
    ipureintro; intro h; cases h
  imod csPts_persist _ _ _ _ $$ HcsB with #HbootCS
  imod isStats_alloc _ ⊤ $$ Stats with #Hstats
  -- the reads' sequence numbers, all at `0`
  imod sync.init_Mutex (readSeqsInv γ «$v5_ptr») ⊤ _ $$ smu [slast Hrseqs] with #Hseqs
  · inext
    unfold readSeqsInv
    iexists W64 0
    isplitl [slast]
    · iExactEq slast; rfl
    iapply (BigSepL.bigSepL_mono (Φ := fun _ i => iprop(i ↪[γ.r.rseq] W64 0))
      (Ψ := fun _ i => iprop(∃ ns : w64, i ↪[γ.r.rseq] ns ∗ ⌜uint.Z ns ≤ uint.Z (W64 0)⌝)) ?_) $$ Hrseqs
    intro _ _ _
    iintro H
    iexists W64 0
    iframe H
    ipureintro; word
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply kvreconf.wp_Mutex_Lock_fresh (cl.[KCluster, go!"mu"])
    (clusterLockInv γ (kvreconf.bootVoters (uint.nat o.Voters')) dir cl) $$ [$Hsync $mu]
    as ⟨#Hmu, Hlocked⟩
  ihave #Hc : isClusterC γ (kvreconf.bootVoters (uint.nat o.Voters')) dir cl $$ []
  · unfold isClusterC
    iexists o, «$v4_ptr», «$v5_ptr»
    simp only [named]
    iframe #
    unfold isReadSeqs
    iframe #
    ipureintro
    exact ⟨⟨⟨HV1, HV5, Hm1, Hm2, Hsz⟩, trivial⟩, Hdup, Hbl0⟩
  -- every voter known: the next-id bound raised at once
  imod mono_nat_own_update (uint.nat o.Voters' + 1) (by omega) $$ HnidA with ⟨HnidA, #Hlb⟩
  try wp_auto
  have Hvnd : (kvreconf.bootVoters (uint.nat o.Voters')).Nodup := kvreconf.bootVoters_nodup _ (by omega)
  ihave IH : iprop(∃ (k : w64) (R : GMap w64 Loc),
      "id" ∷ id_ptr ↦ k ∗ "HR" ∷ mR ↦$ R ∗ "Hcur" ∷ ghostMapAuth γ.cur 1 R ∗
      "%Hk" ∷ ⌜1 ≤ uint.nat k ∧ uint.nat k ≤ uint.nat o.Voters' + 1 ∧
        ∀ i, (R !! i).isSome ↔ 1 ≤ uint.nat i ∧ uint.nat i < uint.nat k⌝ ∗
      "Hreps" ∷ ([∗map] id ↦ r ∈ R, isRep γ (kvreconf.bootVoters (uint.nat o.Voters')) dir id r) ∗
      "Hstops" ∷ ([∗map] id ↦ r ∈ R, (curRep γ id r ∗
        repStop γ (kvreconf.bootVoters (uint.nat o.Voters')) dir id r) ∨ crasher γ) ∗
      "Htodo" ∷ ([∗list] id ∈ (kvreconf.bootVoters (uint.nat o.Voters')).drop (uint.nat k - 1),
        raftState γ.r.cluster id RaftState.init ∗ nodeVacant γ.r.cluster id ∗
        dfile γ.files (kdFileName dir id) none ∗
        ∃ g : RaftState × Option GoString, ghostVar (γ.wr id) (1 : Qp) g))
    $$ [id HR Hcur Hvoters]
  · iexists W64 1, ∅
    iframe id HR Hcur
    simp only [named, show uint.nat (W64 1) - 1 = 0 from rfl, List.drop_zero]
    iframe Hvoters
    isplitr
    · ipureintro; refine ⟨by word, by word, fun i => ?_⟩; simp; word
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    iapply BigSepM.bigSepM_empty.2; itrivial
  wp_for IH
  wp_if_destruct
  · obtain ⟨Hk1, HkV, HdomR⟩ := Hk
    have HkV' : uint.nat k ≤ uint.nat o.Voters' := by word
    have Hnid0 : k ≠ W64 0 := by intro h; subst h; simp at Hk1
    have Hget : (kvreconf.bootVoters (uint.nat o.Voters'))[uint.nat k - 1]? = some k := by
      rw [kvreconf.bootVoters_getElem _ _ (by omega)]; congr 1; word
    rw [kvreconf.life_drop_cons _ _ _ Hget, show uint.nat k - 1 + 1 = uint.nat k from by omega]
    icases Htodo with ⟨⟨HrS, Hvac, Hdf, %g, Hg⟩, Htodo⟩
    imod kdFile_alloc γ dir k ⊤ g $$ Hdf Hg HrS with ⟨#HfInv, Hwr⟩
    ihave #Hknown : repKnown γ k $$ []
    · unfold repKnown
      isplitr
      · ipureintro; exact Hnid0
      iapply monoNatLbOwn_le (uint.nat k + 1) (by omega) $$ Hlb
    try wp_auto
    wp_apply wp_start γ _ dir cl k RaftState.init none (by word) (by word)
      $$ [$Hc $HfInv $Hvac $Hwr $Hknown] as %r ⟨Hr, Hstop⟩
    have HRn : R !! k = none := by
      cases h : R !! k with
      | none => rfl
      | some _ => have := (HdomR k).1 (by simp [h]); omega
    imod ghost_map_insert k r HRn $$ Hcur with ⟨Hcur, Hfrag⟩
    wp_apply wp_mapInsert go.uint64 mR R k r $$ [$HR] as HR
    try wp_auto
    ihave #Hctr := isStats_field (cl.[KCluster, go!"Stats"]) go!"ReplicasStarted" (by decide)
      $$ Hstats
    wp_apply wp_add (cl.[KCluster, go!"Stats"]) _ $$ [$Hpkg $Hctr]
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, <[k := r]> R
    have e2 : uint.nat (k + W64 1) = uint.nat k + 1 := by word
    rw [e2, show uint.nat k + 1 - 1 = uint.nat k from by omega]
    iframe
    isplitr
    · ipureintro
      refine ⟨by omega, by omega, fun i => ?_⟩
      by_cases hi : k = i
      · subst hi; simp; omega
      · rw [GMap.lookup_insert_ne _ _ hi, HdomR]
        have : uint.nat i ≠ uint.nat k := fun h => hi (by word)
        omega
    isplitl [Hreps Hr]
    · iapply (BigSepM.bigSepM_insert (Φ := fun id r => isRep (GF := GF) γ
        (kvreconf.bootVoters (uint.nat o.Voters')) dir id r) (m := R) HRn).2
      iframe Hreps
      unfold isRep
      iexact Hr
    iapply (BigSepM.bigSepM_insert (Φ := fun id r => iprop((curRep (GF := GF) γ id r ∗
      repStop γ (kvreconf.bootVoters (uint.nat o.Voters')) dir id r) ∨ crasher γ)) (m := R) HRn).2
    iframe Hstops
    ileft
    unfold curRep
    iframe Hfrag Hstop
  obtain ⟨Hk1, HkV, HdomR⟩ := Hk
  have HkV' : uint.nat k = uint.nat o.Voters' + 1 := by word
  have HnV : uint.nat (o.Voters' + W64 1) = uint.nat o.Voters' + 1 := by word
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked replicas HR nextID nextOp Hopn HnidA Hjoin
      Hreps Hcur Hstops Hfresh]
  · inext
    unfold clusterLockInv
    iexists mR, R, o.Voters' + W64 1, W64 0, GMap.listToSet (kvreconf.bootVoters (uint.nat o.Voters'))
    rw [HnV]
    rw [kvreconf.bootVoters_length] at *
    simp only [named]
    rw [show (W64 0 : w64) = 0 from rfl]
    iframe
    ipureintro
    refine ⟨fun i => by rw [HdomR, HkV'], fun i => ?_, ?_, by omega⟩
    · rw [GMap.elem_of_list_to_set, kvreconf.bootVoters_mem _ (by omega)]; omega
    · omega
  try wp_auto
  iapply HΦ
  iexact Hc

end proof

end kvdurable
end EtcdGrove
end Perennial
