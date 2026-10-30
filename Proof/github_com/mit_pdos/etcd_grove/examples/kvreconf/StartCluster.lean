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
  imod cluster_alloc (GF := GF) kvrRaftN (bootVoters (uint.nat o.Voters')) [] [] true ⊤ Hrb
    (by intro h; have := congrArg List.length h; rw [bootVoters_length] at this; simp at this; omega)
    (bootVoters_nodup _ (by omega)) (bootVoters_zero _ (by omega))
    (by rw [bootVoters_length]; omega) (fun h => absurd rfl h)
    $$ [] with ⟨%γ, ⟨%Hdup, -⟩, Hops, HU, #Hiscl, Hdec, #Hca0, Hsm, Hjf⟩
  · rw [if_pos rfl]; iempintro
  isimp only [↓reduceIte] at Hjf
  icases Hjf with ⟨Hjoin, Hfounders⟩
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
  generalize hcl : «$r0_ptr» = cl
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
  -- the bootstrap conf state, frozen
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.ConfState «$v3_ptr» _ _ slice.nil [] ⊤ $$ [state sizeCache unknownFields Hnil]
    with #Hpb
  · iframe
  ihave HcsB : csPts «$v3_ptr» (DFrac.own 1) (bootCS (bootVoters (uint.nat o.Voters'))) false
    $$ [HbV Hsv Learners VotersOutgoing LearnersNext AutoLeave]
  · iunfold csPts
    iexists sv, _, _, _, _
    simp only [named, bootCS]
    iframe HbV Hsv Learners VotersOutgoing LearnersNext AutoLeave Hpb
    isplitr
    · ipureintro; exact Hv3nn
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
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_Mutex_Lock_fresh (cl.[RCluster, go!"mu"])
    (clusterLockInv γr (bootVoters (uint.nat o.Voters')) cl) $$ [$Hsync $mu] as ⟨#Hmu, Hlocked⟩
  ihave #Hc : isClusterC γr (bootVoters (uint.nat o.Voters')) cl $$ []
  · unfold isClusterC
    iexists o, «$v3_ptr»
    simp only [named]
    iframe #
    ipureintro
    exact ⟨Hdup, ⟨HV1, HV5, Hm1, Hm2, Hsz⟩, trivial⟩
  try wp_auto
  have HVv : uint.nat o.Voters' ≤ 9 := by omega
  have Hvnd : (bootVoters (uint.nat o.Voters')).Nodup := bootVoters_nodup _ (by omega)
  -- the founders' tokens with their read-sequence elements, and the fresh ids' elements
  ihave Hrseqs : iprop([∗list] id ∈ bootVoters (uint.nat o.Voters') ++ freshIds (uint.nat o.Voters' + 1),
      id ↪[γr.rseq] W64 0) $$ [Hrseqs]
  · rw [allIds_split _ HVv]; iexact Hrseqs
  icases (BigSepL.bigSepL_append (Φ := fun _ id => iprop(id ↪[γr.rseq] W64 0))).1 $$ Hrseqs
    with ⟨Hrs1, Hrseq⟩
  ihave Htodo := (BigSepL.bigSepL_sep_eqv
    (Φ := fun _ id => nodeFounder (GF := GF) γr.cluster kvrRaftN (bootVoters (uint.nat o.Voters')) id)
    (Ψ := fun _ id => (id ↪[γr.rseq] W64 0 : IProp GF)) (l := bootVoters (uint.nat o.Voters'))).2
    $$ [Hfounders Hrs1]
  · iframe Hfounders Hrs1
  ihave IH : iprop(∃ (k : w64) (R : GMap w64 Loc),
      "id" ∷ id_ptr ↦ k ∗ "HR" ∷ mR ↦$ R ∗
      "%Hk" ∷ ⌜1 ≤ uint.nat k ∧ uint.nat k ≤ uint.nat o.Voters' + 1 ∧
        ∀ i, (R !! i).isSome ↔ 1 ≤ uint.nat i ∧ uint.nat i < uint.nat k⌝ ∗
      "Hreps" ∷ ([∗map] id ↦ r ∈ R, isRep γr (bootVoters (uint.nat o.Voters')) id r) ∗
      "Htoks" ∷ ([∗map] _id ↦ r ∈ R, repStop γr (bootVoters (uint.nat o.Voters')) r) ∗
      "Htodo" ∷ ([∗list] id ∈ (bootVoters (uint.nat o.Voters')).drop (uint.nat k - 1),
        nodeFounder γr.cluster kvrRaftN (bootVoters (uint.nat o.Voters')) id ∗ id ↪[γr.rseq] W64 0))
    $$ [id HR Htodo]
  · iexists W64 1, ∅
    iframe id HR
    simp only [named, show uint.nat (W64 1) - 1 = 0 from rfl, List.drop_zero]
    iframe Htodo
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
    have Hget : (bootVoters (uint.nat o.Voters'))[uint.nat k - 1]? = some k := by
      rw [bootVoters_getElem _ _ (by omega)]; congr 1; word
    rw [life_drop_cons _ _ _ Hget, show uint.nat k - 1 + 1 = uint.nat k from by omega]
    icases Htodo with ⟨⟨Hfd, Hseq⟩, Htodo⟩
    try wp_auto
    wp_apply wp_NewMemoryStorage $$ [$Hraft] as %ms %γs' ⟨#Hml, #Hmlog, Hmend, Hmsnap, Hmeta, Hfresh⟩
    try wp_auto
    iStructNamed «$r0»
    imod kvrStor_alloc «$r0_ptr» ms «$v3_ptr» γs' (bootCS (bootVoters (uint.nat o.Voters'))) ⊤
      (fun _ _ => CoPset.mem_full) $$ HstorInv MemoryStorage boot HbootCS with ⟨#Hsrec, #Hsboot⟩
    wp_apply wp_config γr _ cl k «$r0_ptr» Hnid0 (by word) $$ [$Hc] as %cp ⟨%cv, Hcv, %Hcfg⟩
    obtain ⟨HcID, HcSt, HcLg, HcV, HcM, HcDP, HcRO, HcDC, HcSz, HcAS, HcAp⟩ := Hcfg
    ihave Hboot := kvr_bootStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
      wp_Entries «$r0_ptr» ms «$v3_ptr» γs' _ (bootCS (bootVoters (uint.nat o.Voters'))) γr.cluster k
      $$ Hpkg Hsrec Hsboot Hml Hfresh Hmeta Hmlog Hmend
    ihave #Hlogger := qLogger_isLogger wp_Debugf wp_Errorf wp_Infof wp_Warningf
    wp_apply (wp_RestartNode γr.cluster kvrRaftN (bootVoters (uint.nat o.Voters')) cp cv qLogger
        ⟨go.GoType.PointerType rStorageTy, #«$r0_ptr»⟩ (HardStateM.mk (W64 0) (W64 0) (W64 0))
        (bootCS (bootVoters (uint.nat o.Voters')))
        iprop(memStorMeta ms γs' (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
          memStorInvP ms γs' (kvrJ γr.cluster k)) HcV HcLg HcSt HcM HcDP HcRO
        HcDC HcSz HcAS HcAp ⟨rfl, rfl, rfl⟩ rfl rfl rfl rfl rfl)
      $$ [$Hraft $Hcv $Hlogger Hboot Hfd]
      as %nd ⟨%n, %Hnd, #HisNode, Hdrv, Hncfg, Hrun, Hmeta, #HmsInv⟩
    · have Hiface : kvrStorIface «$r0_ptr» =
          GoInterface.ok ⟨go.GoType.PointerType rStorageTy, #«$r0_ptr»⟩ := rfl
      rw [HcID, ← Hiface]
      isplitl [Hboot]
      · iexact Hboot
      ileft
      iexact Hfd
    subst Hnd
    ihave #HisNode' : isNode n γr.cluster kvrRaftN k $$ []
    · rw [← HcID]; iexact HisNode
    have Hiface : kvrStorIface «$r0_ptr» =
        GoInterface.ok ⟨go.GoType.PointerType rStorageTy, #«$r0_ptr»⟩ := rfl
    rw [← Hiface]
    try wp_auto
    wp_apply wp_tick γr _ cl $$ [$Hc] as %tk %Htk
    try wp_auto
    ihave #Hknown : repKnown γr k $$ []
    · unfold repKnown
      isplitr
      · ipureintro; exact Hnid0
      iapply monoNatLbOwn_le (uint.nat k + 1) (by omega) $$ Hlb
    wp_apply wp_sender γr _ cl k $$ [$Hc $Hknown] as %f #Hf
    have Hvl : ((bootVoters (uint.nat o.Voters')).length : Int) < 2 ^ 61 := by
      rw [bootVoters_length]; omega
    wp_apply (wp_newReplica γr _ k n «$r0_ptr» (cl.[RCluster, go!"Stats"]) «$v3_ptr» tk f ms γs' _
        Htk Hvnd Hvl (bootCS_is _ Hvnd))
      $$ [$Hpkg $Hcci $Hcl $Hstats $HisNode' $Hdrv $Hrun $Hncfg $Hsrec $HmsInv $Hmeta $Hmsnap
        $HbootCS $Hf $Hseq] as %r ⟨#Hr, Hrs⟩
    have HRn : R !! k = none := by
      cases h : R !! k with
      | none => rfl
      | some _ => have := (HdomR k).1 (by simp [h]); omega
    wp_apply wp_mapInsert go.uint64 mR R k r $$ [$HR] as HR
    try wp_auto
    ihave #Hctr := isStats_field (cl.[RCluster, go!"Stats"]) go!"ReplicasStarted" (by decide)
      $$ Hstats
    wp_apply wp_add (cl.[RCluster, go!"Stats"]) _ $$ [$Hpkg $Hctr]
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
    isplitl [Hreps]
    · iapply (BigSepM.bigSepM_insert (Φ := fun id r => isRep (GF := GF) γr
        (bootVoters (uint.nat o.Voters')) id r) HRn).2
      iframe Hreps
      iexact Hr
    iapply (BigSepM.bigSepM_insert (Φ := fun _ r => repStop (GF := GF) γr
      (bootVoters (uint.nat o.Voters')) r) HRn).2
    iframe Htoks Hrs
  obtain ⟨Hk1, HkV, HdomR⟩ := Hk
  have HkV' : uint.nat k = uint.nat o.Voters' + 1 := by word
  have HnV : uint.nat (o.Voters' + W64 1) = uint.nat o.Voters' + 1 := by word
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked replicas HR nextID nextOp Hopn HnidA Hjoin
      Hreps Hrseq Hstp1 Htoks]
  · inext
    unfold clusterLockInv
    iexists mR, R, o.Voters' + W64 1, W64 0, listToSet (bootVoters (uint.nat o.Voters')), false
    rw [HnV]
    simp only [named, Bool.false_eq_true, ↓reduceIte]
    rw [show (W64 0 : w64) = 0 from rfl]
    iframe
    ipureintro
    refine ⟨fun i => by rw [HdomR, HkV'], fun i => ?_, ?_, by omega⟩
    · rw [GMap.elem_of_list_to_set, bootVoters_mem _ (by omega)]; omega
    · rw [bootVoters_length]; omega
  try wp_auto
  iapply HΦ
  iexists γr
  iframe Hc Hval
  unfold stopper
  iexact Hstp2

end proof

end kvreconf
end EtcdGrove
end Perennial
