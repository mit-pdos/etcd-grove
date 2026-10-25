/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/StartCluster.lean`. Lean-first (no
Rocq counterpart).

The cluster bring-up of the register's `Main` (until 2026-10-19), at any storage registry
(`[KVStor GF]`): raft's ghost state for the voters `1, 2, 3` (in the dynamic mode of the
cluster's one configuration change, `RemoveMember(3)`: `opR`, `c0R`, `c1R`, `ccOkR`) with the
store's invariant (`rkvInv_alloc`, which gives the client's half at the empty store), the term
budget, then a first loop over the voters (`NewStorage`, `RestartNode` into `peers` and
`storages`), the transfer budget and the `send` closure (`deliver`), and a second loop that
starts each replica (`New`), appends it to `kvs` and forks its `tick`.

**Raft v3.7 (2026-10-16, stage R6b).** `RestartNode` takes the store's storage under the
store's `StorageModel` (`kvStorage_isStorage`) and its `InitialState` closure
(`kvStorage_initialState`); the conf state it returns is `kvConfState clusterIds` (the voters,
no `AutoLeave`: `al = false`, which `RestartNode.spec` admits since stage R6b).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.StartCluster
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.NewStorage
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.Storage__InitialState
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.Storage__Snapshot
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.New
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.deliver
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.tick
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.quietLogger__Debugf
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.quietLogger__Errorf
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.quietLogger__Infof
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.quietLogger__Warningf
public import RaftWitness.Spec.go_etcd_io.raft.v3.RestartNode
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.KVStorageInstance
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Alloc
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.StartLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- The cluster's voters. -/
def clusterIds : List w64 := [W64 1, W64 2, W64 3]

theorem clusterIds_nodup : clusterIds.Nodup := by decide

/-- The cluster has more than one voter. -/
theorem clusterIds_size : 1 < GMap.size (GMap.listToSet clusterIds) := by
  rw [GMap.size_eq_length _ clusterIds clusterIds_nodup]
  · decide
  intro k
  rw [listToSet_constMap, constMap_lookup_isSome]

/-- The cluster has a voter (what `ownRaftGhost_alloc` asks). -/
theorem clusterIds_ne : GMap.listToSet clusterIds ≠ ∅ := by
  intro h
  have := clusterIds_size
  rw [h, GMap.size_empty] at this
  omega

/-! ## The cluster's configuration change (2026-10-15, stage N): removing replica 3

Every conf-change entry of the cluster is `RemoveMember(3)`'s (`ccOkR`, raft's `reCCOk`): the
change `opR` removes voter 3 from `c0R` (the voters 1, 2, 3), giving `c1R` (1, 2), and changes
nothing at `c1R`. -/

/-- The change `RemoveMember(3)` proposes, as `AsV2` makes it. -/
abbrev opR : CCOp := ccV2Of (.v1 (rmCC (W64 3)))

/-- The cluster's initial configuration: the voters 1, 2, 3. -/
abbrev c0R : CCState := cfgState (GMap.listToSet clusterIds) ∅

/-- The configuration after the removal: the voters 1, 2. -/
abbrev c1R : CCState := cfgState (GMap.delete (W64 3) (GMap.listToSet clusterIds)) ∅

/-- The conf-change bytes the cluster admits: `RemoveMember(3)`'s. -/
def ccOkR (ty : w32) (bs : List w8) : Prop :=
  ty = W32 1 ∧ ∃ m, ccDecodeV1 bs = some m ∧ ccV2Of (.v1 m) = opR

theorem clusterIds_size3 : GMap.size (GMap.listToSet clusterIds) = 3 := by
  rw [GMap.size_eq_length _ clusterIds clusterIds_nodup]
  · rfl
  intro k
  rw [listToSet_constMap, constMap_lookup_isSome]

theorem three_mem : W64 3 ∈ GMap.listToSet clusterIds := by
  rw [GMap.elem_of_list_to_set]; decide

theorem three_nmem : W64 3 ∉ (GMap.delete (W64 3) (GMap.listToSet clusterIds) : GSet w64) := by
  rw [GMap.elem_of_gset, GMap.lookup_delete]; simp

theorem delete3_ne : (GMap.delete (W64 3) (GMap.listToSet clusterIds) : GSet w64) ≠ ∅ := by
  intro h
  have h1 : W64 1 ∈ (GMap.delete (W64 3) (GMap.listToSet clusterIds) : GSet w64) := by
    rw [GMap.elem_of_gset, GMap.lookup_delete_ne _ (by decide), ← GMap.elem_of_gset,
      GMap.elem_of_list_to_set]
    decide
  rw [h] at h1
  exact GMap.not_elem_of_empty _ h1

theorem delete3_size : GMap.size (GMap.delete (W64 3) (GMap.listToSet clusterIds) : GSet w64) < 2 ^ 62 := by
  have : GMap.size (GMap.delete (W64 3) (GMap.listToSet clusterIds) : GSet w64) ≤
      GMap.size (GMap.listToSet clusterIds) := by
    apply GMap.subseteq_size
    rw [GMap.elem_of_subseteq]
    intro x hx
    rw [GMap.elem_of_gset] at hx ⊢
    by_cases hk : W64 3 = x
    · subst hk; rw [GMap.lookup_delete] at hx; cases hx
    · rw [GMap.lookup_delete_ne _ hk] at hx; exact hx
  rw [clusterIds_size3] at this
  omega

theorem c0R_ok : CfgOk c0R :=
  cfgOk_cfgState _ clusterIds_ne (by rw [clusterIds_size3]; decide)

theorem c0R_good : CCGood c0R := ccGood_cfgState _

theorem opR_step0 : ccStepB opR c0R = some c1R :=
  ccStepB_removeVoter _ (rmCC (W64 3)) rfl (by unfold rmCC; word) three_mem delete3_ne
    (by rw [clusterIds_size3]; decide)

theorem opR_step1 : ccStepB opR c1R = some c1R :=
  ccStepB_removeAbsent _ (rmCC (W64 3)) rfl (by unfold rmCC; word) three_nmem delete3_ne
    delete3_size

/-- A replica's node, in the cluster's dynamic mode, is at the cluster's conf changes. -/
theorem kvCC_cluster (γn : NodeNames) (Hok : γn.raft.reCCOk = ccOkR)
    (Hmd : γn.mode = .dyn (ccDecOf opR) c0R c0R_ok c0R_good)
    (Hns : γn.raft.reNoSnap = false) : KVCC γn opR c0R c1R :=
  ⟨⟨c0R_ok, c0R_good, Hmd⟩, fun ty bs h => by rw [Hok] at h; exact h, opR_step0, opR_step1, rfl,
    Hns, rfl, rfl⟩

/-- The configuration `StartCluster` starts node `id` with, on the storage `st`. -/
abbrev nodeConfig (id : w64) (st : Loc) : Config :=
  { ID' := id, ElectionTick' := W64 10, HeartbeatTick' := W64 1,
    Storage' := interface.mkOk (go.GoType.PointerType rStorageTy) #st,
    Applied' := 0, AsyncStorageWrites' := false, MaxSizePerMsg' := W64 1048576,
    MaxCommittedSizePerReady' := 0, MaxUncommittedEntriesSize' := 0,
    MaxInflightMsgs' := W64 256, MaxInflightBytes' := 0, CheckQuorum' := false,
    PreVote' := false, ReadOnlyOption' := 0,
    Logger' := interface.mkOk qLoggerTy #qLoggerV,
    DisableProposalForwarding' := false, DisableConfChangeValidation' := false,
    StepDownOnRemoval' := true, TraceLogger' := GoInterface.nil }

theorem nodeConfig_valid (id : w64) (st : Loc) (h : id ∈ clusterIds) :
    ConfigValid (nodeConfig id st) := by
  simp only [clusterIds, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold ConfigValid
  rcases h with rfl | rfl | rfl <;> simp <;> decide

section reg
variable [KVStor GF]

/-- What `StartCluster` holds of a replica between starting its node and starting its replica: the
node's driver token (with the node, `isNode`, in it), the storage's record and the replica's
sequence-number token. -/
def drvRes (γr : RKVNames) (bud : BudgetNames) (id : w64) (nd : GoInterface) (st : Loc) :
    IProp GF :=
  iprop(∃ (γn : NodeNames) (n : Loc),
    ⌜γn.raft = γr.raft ∧ γn.bud = bud ∧ γn.stor = kvStorIface st ∧
      nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
    nodeDriver γn id n [] ∗ (∃ (ms : Loc) (γs : MemStorNames), kvStorRec st ms γs) ∗
    id ↪[γr.seq] W64 0 ∗
    -- (2026-10-15, stage N) the node's mode and the driver's view of its configuration
    ⌜KVCC γn opR c0R c1R⌝ ∗ nodeCfg γn 0 c0R)

theorem StartCluster.wp_proof
    (wp_NewStorage : kvwitness.NewStorage.spec (GF := GF) (hG := hG))
    (wp_InitialState : kvwitness.Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : kvwitness.Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_New : kvwitness.New.spec (GF := GF) (hG := hG))
    (wp_deliver : kvwitness.deliver.spec (GF := GF) (hG := hG))
    (wp_tick : kvwitness.tick.spec (GF := GF) (hG := hG))
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG))
    (wp_RestartNode : RestartNode.spec (GF := GF) (hG := hG)) :
    StartCluster.spec (GF := GF) (hG := hG) := by
  intro vsl Hrb
  wp_start as ⟨#HstorInv, #Hvsl⟩
  rw [show ([W64 1, W64 2, W64 3] : List w64) = clusterIds from rfl]
  ihave %Hvlen := ownSlice_len _ _ _ $$ Hvsl
  have Hvlen3 : sint.Z vsl.len = 3 := by
    have h := Hvlen.1
    simp only [clusterIds, List.length_cons, List.length_nil] at h
    word
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := GoInterface) as %mP HmP
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mS HmS
  -- raft's ghost state for the cluster and the term budget (2026-10-14, stage R) with the
  -- store's invariant, the client's half of the store's state and the sequence-number tokens,
  -- allocated from the client's share once raft's names exist: the store builds the standing
  -- update for raft's own entries (`kv_noopAu`)
  imod raft_dyn_alloc (GF := GF) ⊤ (ccDecOf opR) c0R c0R_ok (GMap.listToSet clusterIds) ccOkR
    (fun γ => iprop(∃ γr : RKVNames, ⌜γr.raft = γ⌝ ∗ rkvInv γr ∗ rkvVal γr kvEmpty ∗
      ([∗map] id ↦ s ∈ constMap clusterIds (W64 0), id ↪[γr.seq] s)))
    (by rw [GMap.elem_of_list_to_set]; decide) $$ []
    with ⟨%γ, %Hcfg', #Hcinv, ⟨%γr, %Hγr, #Hreg, Hval, Hseqs⟩, Hghosts, #Hc0,
      -, #HrdI⟩
  · unfold allocClient
    iintro %γ0 %_ #_ HcL Hfresh HrdF
    imod rkvInv_alloc (GF := GF) ⊤ γ0 (constMap clusterIds (W64 0)) $$ HcL Hfresh HrdF
      with ⟨%γr0, %Hγr0, #Hreg0, Hval0, Hseqs0⟩
    ihave #Hnoop := kv_noopAu γr0 $$ Hreg0
    subst Hγr0
    imodintro
    iframe Hnoop
    iexists γr0
    iframe Hreg0 Hval0 Hseqs0
    ipureintro; rfl
  have Hcfg : γ.reCfg = GMap.listToSet clusterIds := Hcfg'.2.2
  have Hdyn := Hcfg'.1
  have HccOk := Hcfg'.2.1
  -- the term budget (D19b: backed by time receipts; the ticks' credits are the ticking loops'
  -- own receipts)
  imod budget_alloc (GF := GF) Hrb ⊤ with ⟨%bud, #Hbinv, #Hlb0⟩
  rw [listToSet_constMap]
  ihave Hghosts := bigSepM_constMap clusterIds () clusterIds_nodup
    (fun id _ => ownRaftGhostR (GF := GF) γ (ccDecOf opR) c0R id (rinit c0R)) $$ Hghosts
  ihave Hseqs := bigSepM_constMap clusterIds (W64 0) clusterIds_nodup
    (fun id s => (id ↪[γr.seq] s : IProp GF)) $$ Hseqs
  subst Hγr
  ihave Htodo := (BigSepL.bigSepL_sep_eqv
    (Φ := fun _ id => ownRaftGhostR (GF := GF) γr.raft (ccDecOf opR) c0R id (rinit c0R))
    (Ψ := fun _ id => (id ↪[γr.seq] W64 0 : IProp GF)) (l := clusterIds)).2 $$ [Hghosts Hseqs]
  · iframe Hghosts Hseqs
  -- the nodes
  ihave IH1 : iprop(∃ (k : w64) (idv : w64) (M : GMap w64 GoInterface) (S : GMap w64 Loc),
      "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "HmP" ∷ mP ↦$ M ∗ "HmS" ∷ mS ↦$ S ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 3⌝ ∗
      "#Hpeers" ∷ ([∗map] id ↦ nd ∈ M, peerOk γr.raft bud id nd) ∗
      "Hdone" ∷ ([∗list] id ∈ clusterIds.take (sint.nat k), ∃ (nd : GoInterface) (st : Loc),
        ⌜M !! id = some nd ∧ S !! id = some st⌝ ∗ drvRes γr bud id nd st) ∗
      "Htodo" ∷ ([∗list] id ∈ clusterIds.drop (sint.nat k),
        ownRaftGhostR γr.raft (ccDecOf opR) c0R id (rinit c0R) ∗ id ↪[γr.seq] W64 0) ∗
      "%Hdom" ∷ ⌜∀ id, id ∈ clusterIds.drop (sint.nat k) → M !! id = none ∧ S !! id = none⌝)
    $$ [i id HmP HmS Htodo]
  · iexists W64 0, _, ∅, ∅
    iframe i id HmP HmS
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe Htodo
    isplitr
    · ipureintro; constructor <;> word
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    ipureintro; intro id _; exact ⟨rfl, rfl⟩
  wp_for IH1
  wp_if_destruct
  · have Hlt : sint.Z k < 3 := by word
    have Hlt' : sint.nat k < clusterIds.length := by simp [clusterIds]; word
    obtain ⟨id0, Hid0⟩ : ∃ id0, clusterIds[sint.nat k]? = some id0 :=
      ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z vsl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z k) _ DFrac.discard id0 Hk.1 $$ [Hvsl] as -
    · iframe Hvsl; ipureintro; exact Hid0
    wp_apply (wp_NewStorage _ clusterIds) $$ [$HstorInv $Hvsl] as %st ⟨%ms, %γs, #Hrec, #Hvoters, #Hwit, Hmem⟩
    have Hid0m : id0 ∈ clusterIds := List.mem_of_getElem? Hid0
    rw [drop_cons_of_getElem? _ _ _ Hid0]
    icases Htodo with ⟨⟨Hghost, Hseq⟩, Htodo⟩
    ihave #Hlogger := qLogger_isLogger wp_Debugf wp_Errorf wp_Infof wp_Warningf
    ihave #Hstor := kvStorage_isStorage wp_Snapshot st ms γs $$ Hpkg Hrec
    ihave #Hinit := kvStorage_initialState wp_InitialState st _ clusterIds memStorEmpty
      $$ Hpkg Hvoters Hvsl Hwit
    have Hiface : kvStorIface st = GoInterface.ok ⟨go.GoType.PointerType rStorageTy, #st⟩ := rfl
    rw [Hiface]
    ihave Hown : kvOwnStorage (interface.ok ⟨go.GoType.PointerType rStorageTy, #st⟩) memStorEmpty
      $$ [Hmem]
    · unfold kvOwnStorage
      iexists st, ms, γs
      iframe Hrec Hmem
      ipureintro; rfl
    ihave Hown : ownStorage (interface.ok ⟨go.GoType.PointerType rStorageTy, #st⟩) memStorEmpty
      $$ Hown
    ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
    · iPkgInit
    -- (2026-10-19, D21 M2r) out of the no-snapshot mode: nothing committed
    ihave %HnsR : ⌜γr.raft.reNoSnap = false⌝ $$ [Hghost]
    · iunfold ownRaftGhostR at Hghost
      icases Hghost with ⟨Hg, -⟩
      icases ownRaftGhost_noSnap_of_commit γr.raft id0 _ rfl $$ Hg with ⟨%H, -⟩
      ipureintro; exact H
    ihave Hghost : rnInit γr.raft (.dyn (ccDecOf opR) c0R c0R_ok c0R_good) id0
        (GMap.listToSet clusterIds) $$ [Hghost]
    · iunfold rnInit
      isplitr
      · ipureintro; exact ⟨Hdyn, rfl⟩
      iexact Hghost
    wp_apply (wp_RestartNode γr.raft (.dyn (ccDecOf opR) c0R c0R_ok c0R_good)
      bud _ (nodeConfig id0 st) qLogger
      ⟨go.GoType.PointerType rStorageTy, #st⟩ memStorEmpty (HardStateM.mk (W64 0) (W64 0) (W64 0))
      (kvwitness.kvConfState clusterIds)
      (nodeConfig_valid id0 st Hid0m) rfl rfl
      (by show sint.Z (W64 256) < 2 ^ 62; decide) rfl rfl rfl
      (by right; show W64 1048576 ≠ W64 0; decide)
      rfl (fun _ => rfl) rfl rfl rfl (by left; rfl) rfl ⟨rfl, rfl, rfl⟩
      (by decide) clusterIds_nodup (by decide) (by decide) rfl rfl rfl rfl Hcfg Hid0m
      (fun _ => rfl) rfl (.inl rfl))
      $$ [$Hraftinit $«$a0» $Hlogger $Hstor $Hown $Hinit $Hghost $Hc0 $Hbinv $Hlb0]
      as %nd ⟨%γn, %n, %Hnd, #HisNode, Hdrv, Hncfg⟩
    obtain ⟨Hr, Hb, Hs, Hmd, rfl⟩ := Hnd
    have Hdrop := drop_cons_of_getElem? _ _ _ Hid0
    have Hnd' : (clusterIds.drop (sint.nat k)).Nodup := clusterIds_nodup.sublist (List.drop_sublist _ _)
    rw [Hdrop] at Hnd'
    have Hid0n : id0 ∉ clusterIds.drop (sint.nat k + 1) := (List.nodup_cons.mp Hnd').1
    obtain ⟨HM0, HS0⟩ := Hdom id0 (by rw [Hdrop]; exact List.mem_cons_self)
    wp_apply wp_mapInsert go.uint64 mP M id0 _ $$ [$HmP] as HmP
    wp_apply wp_mapInsert go.uint64 mS S id0 st $$ [$HmS] as HmS
    wp_for_post
    iframe
    iexists k + W64 1, id0, <[id0 := interface.mkOk (go.GoType.PointerType node.ty) #n]> M,
      <[id0 := st]> S
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [Hk1, take_succ_of_getElem? _ _ _ Hid0]
    iframe
    isplitr
    · ipureintro; constructor <;> word
    isplitr
    · iapply (BigSepM.bigSepM_insert (Φ := fun id nd => peerOk (GF := GF) γr.raft bud id nd)
        HM0).2
      iframe Hpeers
      unfold peerOk
      iexists γn, n
      iframe HisNode
      ipureintro; exact ⟨Hr, Hb, rfl⟩
    isplitl
    · iapply (BigSepL.bigSepL_append (Φ := fun _ id => iprop(∃ (nd : GoInterface) (st' : Loc),
          ⌜(<[id0 := interface.mkOk (go.GoType.PointerType node.ty) #n]> M) !! id = some nd ∧
            (<[id0 := st]> S) !! id = some st'⌝ ∗ drvRes (GF := GF) γr bud id nd st'))).2
      isplitl [Hdone]
      · iapply (BigSepL.bigSepL_mono (Φ := fun _ id => iprop(∃ (nd : GoInterface) (st' : Loc),
            ⌜M !! id = some nd ∧ S !! id = some st'⌝ ∗ drvRes (GF := GF) γr bud id nd st')) ?_)
          $$ Hdone
        intro j x Hx
        have Hxt : x ∈ clusterIds.take (sint.nat k) := List.mem_of_getElem? Hx
        have Hne : x ≠ id0 := take_drop_ne clusterIds clusterIds_nodup (sint.nat k) x id0 Hxt
          (by rw [Hdrop]; exact List.mem_cons_self)
        iintro ⟨%nd, %st', %Hl, Hres⟩
        iexists nd, st'
        iframe Hres
        ipureintro
        rw [GMap.lookup_insert_ne _ _ (Ne.symm Hne), GMap.lookup_insert_ne _ _ (Ne.symm Hne)]
        exact Hl
      · iapply (BigSepL.bigSepL_singleton (Φ := fun _ id => iprop(∃ (nd : GoInterface) (st' : Loc),
          ⌜(<[id0 := interface.mkOk (go.GoType.PointerType node.ty) #n]> M) !! id = some nd ∧
            (<[id0 := st]> S) !! id = some st'⌝ ∗ drvRes (GF := GF) γr bud id nd st'))).2
        iexists _, st
        isplitr
        · ipureintro; exact ⟨GMap.lookup_insert _ _ _, GMap.lookup_insert _ _ _⟩
        unfold drvRes
        iexists γn, n
        iframe Hdrv Hseq Hncfg
        isplitr
        · ipureintro; exact ⟨Hr, Hb, by rw [Hs]; rfl, rfl⟩
        isplitr
        · iexists ms, γs
          iframe Hrec
        ipureintro; exact kvCC_cluster γn (by rw [Hr]; exact HccOk) Hmd (by rw [Hr]; exact HnsR)
    ipureintro
    intro id Hid
    have Hne : id ≠ id0 := fun h => Hid0n (h ▸ Hid)
    rw [GMap.lookup_insert_ne _ _ (Ne.symm Hne), GMap.lookup_insert_ne _ _ (Ne.symm Hne)]
    exact Hdom id (by rw [Hdrop]; exact List.mem_cons_of_mem _ Hid)
  · have Hk3 : sint.nat k = 3 := by word
    rw [Hk3]
    simp only [show clusterIds.take 3 = clusterIds from rfl, show clusterIds.drop 3 = [] from rfl]
    imod ownMap_persist mP _ M $$ HmP with #HmP
    imod ownMap_persist mS _ S $$ HmS with #HmS
    ipersist peers
    ipersist storages
    -- the transport's transfer budget (2026-10-13): `timeouts` under its lock
    icases typedPointsto_split _ _ _ $$ «$r0» with Htrs
    try simp only [TypedPointsto.typedPointstoDef]
    icases Htrs with ⟨mu, left, -⟩
    imod sync.init_Mutex (transfersInv bud «$r0_ptr») ⊤ («$r0_ptr».[RTransfers, go!"mu"])
      $$ mu [left] with #Htr
    · inext
      unfold transfersInv
      iexists W64 1048576
      iframe left
    ihave #Htr' : isTransfers bud «$r0_ptr» $$ []
    · unfold isTransfers; iexact Htr
    ipersist tr
    ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave Hncap := ownSliceCap_nil (V := Loc) (GF := GF)
    ihave IH2 : iprop(∃ (k : w64) (idv : w64) (ksl : GoSlice) (rs : List Loc),
        "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "kvs" ∷ kvs_ptr ↦ ksl ∗
        "Hks" ∷ ksl ↦* rs ∗ "Hkcap" ∷ ownSliceCap Loc ksl (DFrac.own 1) ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 3⌝ ∗ "%Hrs" ∷ ⌜rs.length = sint.nat k⌝ ∗
        "#Hregs" ∷ ([∗list] r ∈ rs, ∃ γp, isKV γr γp r) ∗
        "Hdrv" ∷ ([∗list] id ∈ clusterIds.drop (sint.nat k), ∃ (nd : GoInterface) (st : Loc),
          ⌜M !! id = some nd ∧ S !! id = some st⌝ ∗ drvRes γr bud id nd st))
      $$ [i id kvs Hnil Hncap Hdone]
    · iexists W64 0, _, slice.nil, []
      iframe i id kvs
      simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
      iframe Hdone
      isplitr
      · iexact Hnil
      isplitr
      · iexact Hncap
      isplitr
      · ipureintro; constructor <;> word
      isplitr
      · ipureintro; rfl
      iapply (BigSepL.bigSepL_nil).2; iempintro
    wp_for IH2
    wp_if_destruct
    · have Hlt : sint.Z k < 3 := by word
      have Hlt' : sint.nat k < clusterIds.length := by simp [clusterIds]; word
      obtain ⟨id0, Hid0⟩ : ∃ id0, clusterIds[sint.nat k]? = some id0 :=
        ⟨_, List.getElem?_eq_getElem Hlt'⟩
      have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z vsl.len := ⟨Hk.1, by word⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z k) _ DFrac.discard id0 Hk.1 $$ [Hvsl] as -
      · iframe Hvsl; ipureintro; exact Hid0
      have Hdrop := drop_cons_of_getElem? _ _ _ Hid0
      rw [Hdrop]
      icases Hdrv with ⟨⟨%nd, %st, %Hlk, Hres⟩, Hdrv⟩
      obtain ⟨HMl, HSl⟩ := Hlk
      unfold drvRes
      icases Hres with ⟨%γn, %n, %Hgn, Hnode, #Hsrec, Hseq, %Hmd, Hncfg⟩
      obtain ⟨Hr, Hb, Hs, rfl⟩ := Hgn
      wp_apply wp_map_lookup1 go.uint64 _ mP M id0 DFrac.discard $$ HmP as -
      wp_apply wp_map_lookup1 go.uint64 _ mS S id0 DFrac.discard $$ HmS as -
      simp only [HMl, HSl, Option.getD_some]
      wp_apply (wp_New γr γn id0 n st _ opR c0R c1R)
          $$ [Hnode Hseq Hncfg]
      · iframe Hreg Hnode Hsrec Hc0 Hseq Hncfg
        isplitr
        · ipureintro; exact Hr
        isplitr
        · ipureintro; exact Hmd
        isplitr
        · ipureintro; exact Hs
        unfold sendSpec
        imodintro
        iintro %msl %ms %Φ'
        imodintro
        iintro ⟨Hmsl, Hmsok, Hcr, Htks⟩ HΦ'
        rw [Hr, Hb]
        wp_auto
        wp_apply (wp_deliver γr.raft bud mP «$r0_ptr» M msl ms)
          $$ [$Hmsl $Hmsok $Hcr $Htks]
        · iframe #
        iapply HΦ'
        itrivial
      iintro %r ⟨%γp, %Hγp, #Hisreg⟩
      wp_apply wp_slice_literal (V := Loc) [r]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hks $Hkcap $Hsl2] as %ksl' ⟨Hks, Hkcap, -⟩
      wp_apply wp_map_lookup1 go.uint64 _ mP M id0 DFrac.discard $$ HmP as -
      simp only [HMl, Option.getD_some]
      ihave #Hpeer := BigSepM.bigSepM_lookup (Φ := fun id nd => peerOk (GF := GF) γr.raft bud id nd)
        HMl $$ Hpeers
      unfold peerOk
      icases Hpeer with ⟨%γn', %n', %Hgn', #HisNode'⟩
      obtain ⟨-, Hb', Hn'⟩ := Hgn'
      have Hnn : n' = n := by
        simp only [interface.mkOk, GoInterface.ok.injEq] at Hn'
        injection Hn' with _ h
        exact (go.intoVal_inj (V := Loc) h).symm
      subst Hnn
      wp_apply wp_fork $$ []
      · wp_apply (wp_tick γn' id0 n') $$ []
        · iframe HisNode'
        itrivial
      wp_for_post
      iframe
      iexists k + W64 1, id0, ksl', rs ++ [r]
      have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      rw [Hk1]
      iframe
      isplitr
      · ipureintro; constructor <;> word
      isplitr
      · ipureintro; simp only [List.length_append, List.length_singleton, Hrs]
      iapply BigSepL.bigSepL_snoc.2
      iframe Hregs
      iexists γp
      iexact Hisreg
    · have Hk3' : sint.nat k = 3 := by word
      iapply HΦ
      iexists γr, rs
      iframe Hks Hval Hregs
      ipureintro; rw [Hrs, Hk3']

end reg

end proof

end kvwitness
end EtcdGrove
end Perennial
