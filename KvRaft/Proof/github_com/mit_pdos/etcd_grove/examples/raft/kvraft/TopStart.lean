/-
# kvraft's start: the global ghost state allocated before any machine runs (2026-11-22)

`notes/kvraft-part.md`, the top-level theorem's start obligation (`Hstart` of the bridge
`Net.robust_of_netFsBoot_addrs`, which has only the global ghost state `G`, no generation): what the
replicas and the checking client share, allocated once.

* `kvraft_store_alloc` (global: `[AllG] [ReceiptGS] [InvGS]`): raft's cluster of the bootstrap voters
  `1 … v` (`cluster_alloc_nb`: duplicating, no bootstrap log, untraced, no snapshot directories, no data
  bound), the conf policy (`kvrRule`), the store's invariant (`rkvInv`, kvdurable's `kd_alloc` without
  its files) at `γ.max = n`, the snapshots' registry, `readyFits`, every replica `1 … n`'s durable state
  and vacancy (the voters' from the allocation, the others' joined: `joinAuth_join`), the client's half
  of the store's state, the operation counter's half and every replica's read sequence number at `0`.
* The protocols' facts at the global level: `kvFacts`, `kvQ` are stated over a heap ghost state
  (`HeapGS`, a generation's) though they read only the global one; the protocols of the replicas'
  addresses are allocated before any generation, so `kvFactsG`/`kvQG` restate them globally, equal by
  `rfl` (`kvFacts_eq`, `kvQ_eq`) to the originals at any `HeapGS`.
* `kvraft_addrs_alloc` (global): every replica address's protocols, from the network's start
  resources (`addrUnset`) and the protocol registry (`regCtx`, `netProto_alloc`).
* Under a generation's `HeapGS`: the pieces as the specs name them (`kdCluster`, `kvCnt`,
  `addrsProto`, `kvPeerAddrs`).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.StartDefs
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.StoreDefs
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Addrs
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Alloc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open raft_kvreconf (readCtxB logHist kvFold bootVoters freshIdsM)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section global
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- The ids `0 … m`: `0`, then `1 … m`. -/
theorem freshIdsM_zero' (m : Nat) : freshIdsM m 0 = W64 0 :: bootVoters m := by
  rw [raft_kvreconf.freshIdsM_cons m 0 (by omega), ← raft_kvreconf.allIdsM_split m 0 (by omega)]
  rfl

/-- **The store's invariant** over raft's cluster `γc` (kvdurable's `kdRkvInv_alloc`, at the global
ghost state): the read sequence of every id `0 … m` at `0`. -/
theorem kvraft_rkvInv_alloc (E : CoPset) (m : Nat) (hm : m < 2 ^ 62) (γc : Cluster) :
    ⊢ ownCommittedOps (GF := GF) γc [] -∗ ownReadCtxs γc ∅ ={E}=∗
      ∃ γ : KdNames, ⌜γ.r.cluster = γc ∧ γ.max = m⌝ ∗ rkvInv γ ∗
        rkvVal γ raft_kvreconf.kvEmpty ∗ ghostVar γ.r.opn (1 : Qp).half (W64 0) ∗
        [∗list] id ∈ freshIdsM m 0, id ↪[γ.r.rseq] W64 0 := by
  iintro Hops HU
  imod ghostVar_alloc (GF := GF) ([] : List (List w8)) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half (GF := GF) γv 1 ([] : List (List w8))).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod ghostVar_alloc (GF := GF) (W64 0) with ⟨%γo, Ho⟩
  icases (ghostVar_split_half (GF := GF) γo 1 (W64 0)).1 $$ Ho with ⟨Ho1, Ho2⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := List w8) with ⟨%γmi, HMi⟩
  imod ghost_map_alloc (GF := GF) (raft_kvreconf.lifeConstMap (freshIdsM m 0) (W64 0))
    with ⟨%γrs, HRS, Hels⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := List w8) with ⟨%γrm, HRM⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × GName) with ⟨%γop, HO⟩
  imod ghost_map_alloc_empty (GF := GF) (K := GName) (V := raft_kvreconf.ReadRec) with ⟨%γrd, HRD⟩
  let γ : KdNames := ⟨⟨γc, γv, γo, γmi, γrs, γrm, γop, 0, 0, γrd⟩, 0, fun _ => 0, 0, 0, m⟩
  imod inv_alloc kdRkvN E (rkvInvBody (GF := GF) γ) $$ [Hops Hv1 HU Ho1 HMi HRS HRM HO HRD]
    with #Hinv
  · inext
    unfold rkvInvBody
    iexists [], W64 0, ∅, raft_kvreconf.lifeConstMap (freshIdsM m 0) (W64 0), ∅, ∅, ∅
    isplitl [Hops Hv1 HU Ho1 HMi HRS HRM HO]
    · unfold kvCore
      simp only [show logHist ([] : List LogEntry) = [] from rfl]
      iframe Hops Hv1 HU Ho1 HMi HRS HRM HO
      ipureintro
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · intro i d h; simp at h
      · intro r s c h; simp at h
      · intro d γp h; simp at h
      · intro c h; rw [GMap.elem_of_gset] at h; simp at h
      · intro d h; simp at h
      · intro e h; simp at h
    · isplitl []
      · iapply BigSepM.bigSepM_empty.2
        itrivial
      unfold readReg
      iexists ∅
      iframe HRD
      iapply BigSepM.bigSepM_empty.2
      itrivial
  imodintro
  iexists γ
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  unfold rkvInv rkvVal
  iframe Hinv Ho2
  isplitl [Hv2]
  · iexists []
    iframe Hv2
    ipureintro; rfl
  have Hnd : (freshIdsM m 0).Nodup := by
    rw [freshIdsM_zero' m]
    exact List.nodup_cons.2 ⟨raft_kvreconf.bootVoters_zero m hm, raft_kvreconf.bootVoters_nodup m hm⟩
  ihave Hl := raft_kvreconf.bigSepM_keys (fun k x => iprop(k ↪[γrs] x)) (freshIdsM m 0)
    (raft_kvreconf.lifeConstMap (freshIdsM m 0) (W64 0)) Hnd
    (fun k => by rw [raft_kvreconf.lifeConstMap_lookup]; split <;> simp_all) $$ Hels
  iapply (BigSepL.bigSepL_mono (Φ := fun _ k => iprop(∃ x,
    ⌜raft_kvreconf.lifeConstMap (freshIdsM m 0) (W64 0) !! k = some x⌝ ∗ k ↪[γrs] x)) ?_) $$ Hl
  intro j k hj
  iintro ⟨%x, %hx, H⟩
  rw [raft_kvreconf.lifeConstMap_lookup, ite_eq_left (List.mem_of_getElem? hj)] at hx
  cases hx
  iexact H

/-- **The registry of the snapshots made**, none yet. -/
theorem kvraft_snapInv_alloc (γ : KdNames) (E : CoPset) :
    ⊢ ownSnapsMade (GF := GF) γ.r.cluster [] ={E}=∗ kdSnapInv γ := by
  iintro H
  unfold kdSnapInv
  iapply inv_alloc
  inext
  iexists []
  iframe H
  iapply (BigSepL.bigSepL_nil).2; iempintro

/-- `bootVoters (k + 1)` is `bootVoters k` and then `k + 1`. -/
theorem bootVoters_succ (k : Nat) : bootVoters (k + 1) = bootVoters k ++ [W64 ((k : Int) + 1)] := by
  simp [bootVoters, List.range_succ]

/-- `k + 1` is not among `1 … k` (below `2^62`). -/
theorem bootVoters_succ_not_mem (k : Nat) (hk : k + 1 < 2 ^ 62) :
    W64 ((k : Int) + 1) ∉ bootVoters k := by
  have Hnd := raft_kvreconf.bootVoters_nodup (k + 1) (by omega)
  rw [bootVoters_succ] at Hnd
  intro h
  exact (List.nodup_append.1 Hnd).2.2 _ h _ (List.mem_singleton_self _) rfl

/-- **The replicas past the bootstrap voters joined**: from the join authority of `1 … v`, the durable
state and vacancy of every id `v + 1 … n`. -/
theorem kvraft_join_upto (γc : Cluster) (N : Namespace) (v : Nat) :
    ∀ d : Nat, v + d < 2 ^ 62 →
    ⊢ isCluster (GF := GF) γc N -∗ joinAuth γc (GMap.listToSet (bootVoters v)) ==∗
      joinAuth γc (GMap.listToSet (bootVoters (v + d))) ∗
      [∗list] id ∈ (bootVoters (v + d)).drop v, raftState γc id RaftState.init ∗ nodeVacant γc id
  | 0, _ => by
    iintro - Hj
    imodintro
    simp only [Nat.add_zero]
    rw [List.drop_eq_nil_of_le (by rw [raft_kvreconf.bootVoters_length]; exact Nat.le_refl _)]
    iframe Hj
    iapply (BigSepL.bigSepL_nil).2; iempintro
  | d + 1, hd => by
    iintro #Hc Hj
    imod kvraft_join_upto γc N v d (by omega) $$ Hc Hj with ⟨Hj, Hs⟩
    have hx := bootVoters_succ_not_mem (v + d) (by omega)
    imod joinAuth_join γc N _ (W64 (((v + d : Nat) : Int) + 1))
      (fun h => hx ((GMap.elem_of_list_to_set _ _).1 h))
      (fun h => raft_kvreconf.bootVoters_zero (v + d + 1) (by omega)
        (by rw [bootVoters_succ, ← h]; exact List.mem_append_right _ (List.mem_singleton_self _)))
      $$ [Hc Hj] with ⟨Hj, Hr, Hn⟩
    · iframe Hc Hj
    imodintro
    have hb : bootVoters (v + (d + 1)) = bootVoters (v + d) ++ [W64 (((v + d : Nat) : Int) + 1)] := by
      rw [show v + (d + 1) = v + d + 1 by omega, bootVoters_succ]
    rw [hb]
    have hset : GMap.listToSet (bootVoters (v + d) ++ [W64 (((v + d : Nat) : Int) + 1)]) =
        {[W64 (((v + d : Nat) : Int) + 1)]} ∪ GMap.listToSet (bootVoters (v + d)) := by
      apply GMap.set_eq; intro x
      rw [GMap.elem_of_list_to_set, GMap.elem_of_union, GMap.elem_of_singleton,
        GMap.elem_of_list_to_set, List.mem_append, List.mem_singleton]
      constructor <;> intro h <;> rcases h with h | h <;> simp_all
    rw [hset, List.drop_append_of_le_length (by rw [raft_kvreconf.bootVoters_length]; omega)]
    iframe Hj
    iapply BigSepL.bigSepL_append.2
    iframe Hs
    iapply BigSepL.bigSepL_cons.2
    iframe Hr Hn
    iapply (BigSepL.bigSepL_nil).2; iempintro

/-- A big separating conjunction over a list, from its parts before and after `k`. -/
theorem bigSepL_take_drop' {A : Type} (Φ : A → IProp GF) (l : List A) (k : Nat) :
    ([∗list] x ∈ l.take k, Φ x) ∗ ([∗list] x ∈ l.drop k, Φ x) ⊢ [∗list] x ∈ l, Φ x := by
  conv => rhs; rw [← List.take_append_drop k l]
  exact BigSepL.bigSepL_append.2

/-- **kvraft's store, allocated before any machine runs** (see the file header), for `n` replicas of
which `1 … v` are the bootstrap voters. -/
theorem kvraft_store_alloc (E : CoPset) (n v : Nat) (hv1 : 1 ≤ v) (hvn : v ≤ n) (hn : n < 2 ^ 32)
    (Hrb : receiptBound GF ≤ 2 ^ 61) :
    ⊢ |={E}=> ∃ γ : KdNames,
      ⌜γ.max = n ∧ γ.r.cluster.dup = true ∧ γ.r.cluster.bootLen = 0 ∧
        Cluster.trace γ.r.cluster = none ∧ γ.r.cluster.snapLoc = (fun _ => none) ∧
        γ.r.cluster.maxData = none⌝ ∗
      isCluster γ.r.cluster kdRaftN ∗ confPolicy γ.r.cluster kdConfN raft_kvreconf.kvrRule ∗
      confAt γ.r.cluster 0 (Membership.simple (GMap.listToSet (bootVoters v))) ∗ kdSnapInv γ ∗
      rkvInv γ ∗ readyFits γ.r.cluster kdRaftN ∗
      ([∗list] id ∈ bootVoters n, raftState γ.r.cluster id RaftState.init ∗
        nodeVacant γ.r.cluster id) ∗
      rkvVal γ raft_kvreconf.kvEmpty ∗ ghostVar γ.r.opn (1 : Qp).half (W64 0) ∗
      [∗list] id ∈ bootVoters n, id ↪[γ.r.rseq] W64 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvn
  have Hlen := raft_kvreconf.bootVoters_length v
  imod cluster_alloc_nb (GF := GF) kdRaftN (bootVoters v) true (fun _ => none) none E
    (by omega) (by intro h; rw [h] at Hlen; simp at Hlen; omega)
    (raft_kvreconf.bootVoters_nodup _ (by omega)) (raft_kvreconf.bootVoters_zero _ (by omega))
    (by rw [Hlen]; omega) (fun _ h => by cases h) with
    ⟨%γc, %Hd, -, %Htr, Hops, HU, #Hcl, Hdec, #Hca, Hsm, Hrs, Hja⟩
  imod confPolicy_alloc γc kdConfN raft_kvreconf.kvrRule E $$ Hdec with #Hpol
  imod kvraft_join_upto γc kdRaftN v d (by omega) $$ Hcl Hja with ⟨-, Hrs2⟩
  imod kvraft_rkvInv_alloc E (v + d) (by omega) γc $$ Hops HU with ⟨%γ, %Hγ, Hinv, Hval, Hopn, Hrseq⟩
  obtain ⟨Hγc, Hγm⟩ := Hγ
  subst Hγc
  imod kvraft_snapInv_alloc γ E $$ Hsm with Hsnap
  imodintro
  iexists γ
  rw [freshIdsM_zero' (v + d)]
  icases BigSepL.bigSepL_cons.1 $$ Hrseq with ⟨-, Hrseq⟩
  iframe Hcl Hpol Hca Hsnap Hinv Hval Hopn Hrseq
  isplitr
  · ipureintro; exact ⟨Hγm, Hd.1, Hd.2.2.1, Htr, Hd.2.1, Hd.2.2.2⟩
  isplitr
  · iapply readyFits_intro
    rw [Hd.2.2.1]; omega
  have htake : (bootVoters (v + d)).take v = bootVoters v := by
    rw [← raft_kvreconf.allIdsM_split (v + d) v hvn]
    exact List.take_left' Hlen
  iapply bigSepL_take_drop' _ _ v
  rw [htake]
  iframe Hrs Hrs2

end global

/-! ## The protocols' facts, at the global ghost state -/

section factsG
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- `readOkK`, at the global ghost state. -/
def readOkG (γ : KdNames) (id seq : w64) (key : List w8) : IProp GF :=
  iprop(⌜(key.length : Int) < 2 ^ 61⌝ ∗ (id, seq) ↪[γ.r.rmint]□ readCtxB id seq key ∗
    isReadCtx γ.r.cluster kdRaftN (readCtxB id seq key) (fun _ => iprop(True)) ∗
    ∃ l0 : List LogEntry, readCtxAfter γ.r.cluster kdRaftN (readCtxB id seq key) l0 ∗
      isCommittedLogLb γ.r.cluster l0)

/-- `ansReadK`, at the global ghost state. -/
def ansReadG (γ : KdNames) (id seq : w64) (key v : List w8) : IProp GF :=
  iprop(∃ (l0 : List LogEntry) (L : List (List w8)),
    readCtxAfter γ.r.cluster kdRaftN (readCtxB id seq key) l0 ∗ kvLb γ L ∗
    ⌜logHist l0 <+: L ∧ v = kvFold L key⌝)

/-- `msgOkK`, at the global ghost state. -/
def msgOkG (γ : KdNames) (src : w64) (st : MsgSt) : IProp GF :=
  iprop(sentMsg γ.r.cluster kdRaftN src st ∗ □ msgCredits γ.r.cluster kdRaftN st ∗ ⌜MsgWf st⌝)

/-- `kvFacts`, at the global ghost state. -/
def kvFactsG (γ : KdNames) (cf : List w8 → Prop) : KvFacts GF where
  msgOk := msgOkG γ
  opOk := fun d => iprop(∃ γp : GName × GName, d ↪[γ.r.ops]□ γp)
  readOk := readOkG γ
  confOk := cf
  ansOp := waitP γ
  ansRead := ansReadG γ
  msgOk_pers := fun src st => by unfold msgOkG; infer_instance
  opOk_pers := fun d => by infer_instance
  readOk_pers := fun id seq key => by unfold readOkG; infer_instance
  ansOp_pers := fun d v => by unfold waitP; infer_instance
  ansRead_pers := fun id seq key v => by unfold ansReadG kvLb; infer_instance
  msgOk_wf := fun src st => by
    unfold msgOkG
    iintro ⟨-, -, %H⟩
    ipureintro; exact H

end factsG

section protoG
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [Net.NetProtoGS]
variable (F : KvFacts GF)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `kvQ`, at the global ghost state. -/
def kvQG (id : w64) : Net.Proto GF := fun cn ext =>
  iprop(⌜ext = [] ∨ ext = putB [W8 0]⌝ ∨
    ∃ kind tmo pl v, Net.sentLb cn false (helloClientB :: putB (reqBytes kind tmo pl)) ∗
      ⌜ext = putB (W8 1 :: v) ∧ (reqBytes kind tmo pl).length < 2 ^ 63 ∧ v.length < 2 ^ 63⌝ ∗
      ansOk F id kind pl v)

/-- Every address of `addrs` gets its protocols, those of the replica `k + i + 1` at the `i`-th. -/
theorem kvraft_addrs_set (E : CoPset) (P Q : w64 → Net.Proto GF) :
    ∀ (addrs : List GoString) (k : Nat),
    ⊢ Net.regCtx (Gg := Gg) -∗ ([∗list] a ∈ addrs, Net.addrUnset a) ={E}=∗
      [∗list] i ↦ a ∈ addrs, Net.addrProto a (P (W64 (((k + i : Nat) : Int) + 1)))
        (Q (W64 (((k + i : Nat) : Int) + 1)))
  | [], _ => by
    iintro - -
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | a :: addrs, k => by
    iintro #Hreg Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hu, Hs⟩
    imod Net.addr_set_proto E a (P (W64 (((k + 0 : Nat) : Int) + 1)))
      (Q (W64 (((k + 0 : Nat) : Int) + 1))) $$ Hreg Hu with #Hp
    imod kvraft_addrs_set E P Q addrs (k + 1) $$ Hreg Hs with Hps
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hp
    iapply (BigSepL.bigSepL_mono ?_) $$ Hps
    intro i b _
    rw [show k + 1 + i = k + (i + 1) by omega]

/-- **The replicas' addresses' protocols** (see the file header): replica `i + 1`'s at the `i`-th
address, kvraft's protocols at the facts `F` (at the top, `kvFactsG γ (fun _ => True)`). -/
theorem kvraft_addrs_alloc (E : CoPset) (addrs : List GoString) :
    ⊢ Net.regCtx (Gg := Gg) -∗ ([∗list] a ∈ addrs, Net.addrUnset a) ={E}=∗
      [∗list] i ↦ a ∈ addrs, Net.addrProto a (kvP F (W64 ((i : Int) + 1))) (kvQG F (W64 ((i : Int) + 1))) := by
  iintro #Hreg Hs
  imod kvraft_addrs_set E (kvP F) (kvQG F) addrs 0 $$ Hreg Hs with Hps
  imodintro
  iapply (BigSepL.bigSepL_mono ?_) $$ Hps
  intro i b _
  rw [Nat.zero_add]

end protoG

/-! ## Under a generation's heap ghost state: the pieces as the specs name them -/

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- `kvFacts` is `kvFactsG`. -/
theorem kvFacts_eq (γ : KdNames) (cf : List w8 → Prop) :
    kvFacts (GF := GF) γ cf = kvFactsG γ cf := rfl

/-- `kvQ` is `kvQG`. -/
theorem kvQ_eq (F : KvFacts GF) (id : w64) : kvQ F id = kvQG F id := rfl

/-- The store's cluster, from its allocated pieces. -/
theorem kvraft_kdCluster (γ : KdNames) (vs : List w64) :
    ⊢ isCluster (GF := GF) γ.r.cluster kdRaftN -∗ confPolicy γ.r.cluster kdConfN raft_kvreconf.kvrRule -∗
      confAt γ.r.cluster 0 (Membership.simple (GMap.listToSet vs)) -∗ kdSnapInv γ -∗ rkvInv γ -∗
      ⌜Cluster.trace γ.r.cluster = none⌝ -∗ kdCluster γ vs := by
  iintro Hc Hp Ha Hs Hi %Ht
  unfold kdCluster
  iframe Hc Hp Ha Hs Hi
  ipureintro; exact Ht

/-- The checker's operation counter at `0`, from the store's half. -/
theorem kvraft_kvCnt_op (γ : KdNames) (n : Nat) :
    ghostVar (GF := GF) γ.r.opn (1 : Qp).half (W64 0) ⊢ raft_kvcheck.kvCnt γ n false (W64 0) := by
  unfold raft_kvcheck.kvCnt
  exact .rfl

/-- The checker's read counter at `0`, from every replica's read sequence number. -/
theorem kvraft_kvCnt_read (γ : KdNames) (n : Nat) :
    ([∗list] id ∈ bootVoters n, id ↪[γ.r.rseq] W64 0) ⊢
      raft_kvcheck.kvCnt (GF := GF) γ n true (W64 0) := by
  unfold raft_kvcheck.kvCnt
  simp only [↓reduceIte]
  iintro H
  iapply (BigSepL.bigSepL_mono ?_) $$ H
  intro k id _
  iintro H
  iexists W64 0
  iframe H
  ipureintro; exact Int.le_refl _

/-- The checking client's addresses' protocols (`Check`'s `addrsProto`), from the allocated ones. -/
theorem kvraft_addrsProto (γ : KdNames) (cf : List w8 → Prop) (ls : List GoString)
    (hok : ∀ a ∈ ls, Net.addrOk a = true) :
    ([∗list] i ↦ a ∈ ls, Net.addrProto a (kvP (kvFactsG γ cf) (W64 ((i : Int) + 1)))
      (kvQG (kvFactsG γ cf) (W64 ((i : Int) + 1)))) ⊢
      raft_kvcheck.addrsProto (kvFacts (GF := GF) γ cf) ls := by
  unfold raft_kvcheck.addrsProto
  iintro H
  iapply (BigSepL.bigSepL_mono ?_) $$ H
  intro i a hi
  iintro H
  isplitr
  · ipureintro; exact hok a (List.mem_of_getElem? hi)
  rw [kvFacts_eq, kvQ_eq]
  iexact H

/-- **The other replicas' addresses** (`kvPeerAddrs`, `StartNode`'s), for an address map `M` holding
exactly the addresses `ls`, from the allocated protocols. -/
theorem kvraft_peerAddrs (γ : KdNames) (ls : List GoString) (id : w64) (M : GMap w64 GoString)
    (hM : addrMapOk ls M) (hok : ∀ a ∈ ls, Net.addrOk a = true) :
    □ ([∗list] i ↦ a ∈ ls, Net.addrProto a (kvP (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))
      (kvQG (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))) ⊢
      kvPeerAddrs (GF := GF) γ id M := by
  unfold kvPeerAddrs
  iintro #H
  imodintro
  iintro %pid %a %h
  obtain ⟨hpa, -⟩ := h
  have hl := hM pid
  rw [hpa] at hl
  split at hl
  · rename_i h1
    have hget : ls[uint.nat pid - 1]? = some a := hl.symm
    have hid : W64 (((uint.nat pid - 1 : Nat) : Int) + 1) = pid := by
      rw [show (((uint.nat pid - 1 : Nat) : Int) + 1) = (uint.nat pid : Int) by omega]; word
    ihave Ha := BigSepL.bigSepL_lookup (Φ := fun i a => Net.addrProto a
      (kvP (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))
      (kvQG (kvFactsG γ (fun _ => True)) (W64 ((i : Int) + 1)))) hget $$ H
    rw [hid, kvFacts_eq, kvQ_eq]
    iframe Ha
    ipureintro; exact hok a (List.mem_of_getElem? hget)
  · cases hl

end heap

end kvraft
end EtcdGrove
end Perennial
