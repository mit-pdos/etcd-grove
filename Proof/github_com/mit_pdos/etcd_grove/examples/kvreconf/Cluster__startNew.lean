/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__startNew.lean`. Lean-first
(no Rocq counterpart).

Under `c.mu`: with fewer than `maxReplicas` replicas (the map's keys are `1 … nextID-1`, so
`nextID ≤ 9`), the fresh id `nextID` is joined (`joinAuth_join`: not among the started ids; its
durable state at `RaftState.init` and its vacant id), its storage allocated and registered
(`kvrStor_alloc`), its node restarted from the fresh storage (`RestartNode`, the bootstrap voters at
`0` from the store's cluster, its update fired at once, `kvr_restartAu`; 2026-11-01, durability
stage II (l)), its
transport made (`sender`, `repKnown` from the raised `γr.nid` bound) and the replica started
(`newReplica`, with the id's read-sequence element from the lock's `freshIds`). The replica and its
stop tokens (unless the stopper took them) go into the lock.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__startNew
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__config
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__tick
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__sender
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.newReplica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.StartLemmas
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

theorem Cluster.startNew.wp_proof
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
    Cluster.startNew.spec (GF := GF) (hG := hG) := by
  intro γr vs c
  wp_start as #Hc
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold clusterLockInv at HL
  iNamed HL
  obtain ⟨HdomR, HdomU, Hvn, Hn10⟩ := Hdom
  have Hsz : GMap.size R = uint.nat nid - 1 := size_of_keys R (uint.nat nid) Hn10 (by omega) HdomR
  try wp_auto
  wp_apply wp_map_len_lt mR R _ $$ [$HR] as ⟨HR, %Hlt⟩
  wp_if_destruct
  · -- `maxReplicas` started: nothing changes
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hreps
      Hrseq Hstp Htoks]
    · inext
      unfold clusterLockInv
      iexists mR, R, nid, nop, U, b
      iframe
      ipureintro; exact ⟨HdomR, HdomU, Hvn, Hn10⟩
    try wp_auto
    iapply HΦ; itrivial
  have Hn9 : uint.nat nid < 10 := by word
  try wp_auto
  wp_apply wp_NewMemoryStorage $$ [$Hraft] as %ms %γs ⟨#Hml, #Hmlog, Hmend, Hmsnap, Hmeta, Hfresh⟩
  try wp_auto
  iStructNamed «$r0»
  imod kvrStor_alloc «$r0_ptr» ms bp γs (bootCS vs) ⊤ (fun _ _ => CoPset.mem_full)
    $$ HstorInv MemoryStorage boot HbootCS with ⟨#Hsrec, #Hsboot⟩
  have Hnid0 : nid ≠ W64 0 := by intro h; rw [h] at Hvn; simp at Hvn
  wp_apply wp_config γr vs c nid «$r0_ptr» Hnid0 (by word) $$ [$Hc] as %cp ⟨%cv, Hcv, %Hcfg⟩
  obtain ⟨HcID, HcSt, HcLg, HcV, HcM, HcDP, HcRO, HcDC, HcSz, HcAS, HcAp⟩ := Hcfg
  have Hvnd : vs.Nodup := by rw [Ho.2]; exact bootVoters_nodup _ (by have := Ho.1.2.1; word)
  ihave #Hcl' := Hcl
  iunfold kvrCluster at Hcl'
  icases Hcl' with ⟨#Hic, -, #Hca0, -, -⟩
  have HnU : nid ∉ U := by rw [HdomU]; omega
  imod joinAuth_join γr.cluster kvrRaftN U nid HnU Hnid0 $$ [$Hic $Hjoin] with ⟨Hjoin, HrS, Hvac⟩
  ihave Hboot := kvr_bootStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
    wp_Entries «$r0_ptr» ms bp γs _ (bootCS vs) γr.cluster
    (fun K => iprop(memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
      memStorInvP ms γs (kvrJ γr.cluster K)))
    $$ Hpkg Hsrec Hsboot Hml Hfresh Hmeta Hmlog Hmend []
  · iintro %K Hm Hi; iframe Hm Hi
  ihave Hau := kvr_restartAu γr.cluster kvrRaftN nid kvrBootContents kvrBoot_holds $$ HrS
  ihave #Hlogger := qLogger_isLogger wp_Debugf wp_Errorf wp_Infof wp_Warningf
  have Hiface : kvrStorIface «$r0_ptr» =
      GoInterface.ok ⟨go.GoType.PointerType rStorageTy, #«$r0_ptr»⟩ := rfl
  wp_apply (wp_RestartNode γr.cluster kvrRaftN cp cv qLogger
      ⟨go.GoType.PointerType rStorageTy, #«$r0_ptr»⟩ kvrBootContents (bootCS vs) 0
      (Membership.simple (GMap.listToSet vs))
      (fun S => iprop(raftState γr.cluster nid S ∗ ⌜S = RaftState.init⌝))
      (fun K => iprop(memStorMeta ms γs (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗
        memStorInvP ms γs (kvrJ γr.cluster K)))
      HcV HcLg HcSt HcM HcDP HcRO HcDC HcSz HcAS (Or.inl (by rw [HcAp]; rfl))
      (by rw [HcAp]; simp [StorContents.b]) (by simp [StorContents.commit])
      (by rw [Hbl0]; simp [StorContents.commit]) (bootCS_is vs Hvnd))
    $$ [$Hraft $Hcv $Hlogger Hboot Hvac Hau]
    as %nd ⟨%n, %S, %l, %K, %Hnd, #HisNode, #Hl, %Hlen, Hdrv, Hncfg, Hrun, ⟨HrS, %HS⟩, Hmeta, #HmsInv⟩
  · have hA : uint.nat cv.Applied' = 0 := by rw [HcAp]; rfl
    rw [HcID, ← Hiface, hA]
    iframe Hboot Hvac Hic Hca0
    iExactEq Hau; rfl
  subst Hnd
  have Hl0 : l = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen, HcAp]; rfl)
  rw [kvr_startDriver _ l K S Hl0 HS] at *
  subst HS
  ihave #HisNode' : isNode n γr.cluster kvrRaftN nid $$ []
  · rw [← HcID]; iexact HisNode
  rw [← Hiface]
  try wp_auto
  wp_apply wp_tick γr vs c $$ [$Hc] as %tk %Htk
  try wp_auto
  -- the new id is known: the next-id bound raised
  imod mono_nat_own_update (uint.nat nid + 1) (by omega) $$ HnidA with ⟨HnidA, #Hlb⟩
  ihave #Hknown : repKnown γr nid $$ []
  · unfold repKnown; iframe Hlb; ipureintro; exact Hnid0
  wp_apply wp_sender γr vs c nid $$ [$Hc $Hknown] as %f #Hf
  -- the id's read-sequence element
  have e2 : uint.nat (nid + W64 1) = uint.nat nid + 1 := by word
  have Hfr : freshIds (uint.nat nid) = nid :: freshIds (uint.nat (nid + W64 1)) := by
    rw [freshIds_cons _ Hn9, e2]; congr 1; word
  ihave Hrseq : iprop([∗list] i ∈ nid :: freshIds (uint.nat (nid + W64 1)), i ↪[γr.rseq] W64 0)
    $$ [Hrseq]
  · rw [← Hfr]; iexact Hrseq
  icases (BigSepL.bigSepL_cons (Φ := fun _ i => iprop(i ↪[γr.rseq] W64 0))).1 $$ Hrseq
    with ⟨Hseq, Hrseq⟩
  have Hvl : (vs.length : Int) < 2 ^ 61 := by
    rw [Ho.2, bootVoters_length]; have := Ho.1.2.1; word
  wp_apply (wp_newReplica γr vs nid n «$r0_ptr» (c.[RCluster, go!"Stats"]) bp tk f ms γs _ K Htk Hvnd
      Hvl (bootCS_is vs Hvnd))
    $$ [$Hpkg $Hcci $Hcl $Hstats $HisNode' $Hdrv $HrS $Hrun $Hncfg $Hsrec $HmsInv $Hmeta $Hmsnap
      $HbootCS $Hf $Hseq] as %r ⟨#Hr, Hrs⟩
  have HRn : R !! nid = none := by
    cases h : R !! nid with
    | none => rfl
    | some _ => have := (HdomR nid).1 (by simp [h]); omega
  wp_apply wp_mapInsert go.uint64 mR R nid r $$ [$HR] as HR
  try wp_auto
  ihave #Hctr := isStats_field (c.[RCluster, go!"Stats"]) go!"ReplicasStarted" (by decide) $$ Hstats
  wp_apply wp_add (c.[RCluster, go!"Stats"]) _ $$ [$Hpkg $Hctr]
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked HmR HR Hnid Hnop Hopn HnidA Hjoin Hreps Hr
      Hrseq Hstp Htoks Hrs]
  · inext
    unfold clusterLockInv
    iexists mR, <[nid := r]> R, nid + W64 1, nop, {nid} ∪ U, b
    rw [e2]
    iframe Hnid Hnop Hopn HnidA Hjoin HmR HR Hrseq Hstp
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
    isplitl [Hreps]
    · iapply (BigSepM.bigSepM_insert (Φ := fun id r => isRep (GF := GF) γr vs id r) HRn).2
      iframe Hreps
      iexact Hr
    cases b with
    | true => simp only [↓reduceIte]; itrivial
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      iapply (BigSepM.bigSepM_insert (Φ := fun _ r => repStop (GF := GF) γr vs r) HRn).2
      iframe Htoks Hrs
  try wp_auto
  iapply HΦ
  itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
