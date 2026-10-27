/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/StartClusterWitness.lean`. Lean-first
(2026-10-20, W4).

`StartCluster`'s bring-up (`StartCluster.lean`), in raft's static mode at the members `1, 2, 3`
with the witness `3` (`ownRaftGhost_alloc_core` at the witness: no node runs at it; the cluster
admits no conf-change entry, `ccOk` false): the store's invariant, the term budget, then a first
loop over the regular voters `1, 2` (each a `Storage` on a fresh `MemoryStorage` whose conf state
is the members and the witness, `RestartNode` at it: `RestartNode.spec`'s witness case), the
transfer budget and the `send` closure (`deliver`), the shared `WitnessStore` (its states' ghost
counterpart the witness's protocol history and the term budget: `wGhost`, `termLB`), and a second
loop that gives each replica its own `Witness` on the store (`NewWitness`, `ownWitnessIT`), starts
it (`newKV`), appends it to `kvs` and forks its `tick`.
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.StartClusterWitness
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.copyIDs
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.Storage__InitialState
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.Storage__Snapshot
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.newKV
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.deliver
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.tick
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.NewWitnessStore
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.WitnessStore__GetWitnessState
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.WitnessStore__Close
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.witnessRead__GetState
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.witnessRead__Update
public import RaftWitness.Spec.go_etcd_io.raft.v3.RestartNode
public import RaftWitness.Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import RaftWitness.Spec.go_etcd_io.raft.v3.NewWitness
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.KVStorageInstance
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.WitnessStorageInstance
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Alloc
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.StartLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- The cluster's regular voters, each running a replica. -/
def votersW : List w64 := [W64 1, W64 2]

/-- The cluster's members: the regular voters and the witness `3`. -/
def membersW : List w64 := [W64 1, W64 2, W64 3]

theorem votersW_nodup : votersW.Nodup := by decide
theorem membersW_nodup : membersW.Nodup := by decide

theorem membersW_ne : GMap.listToSet membersW ≠ ∅ := by
  intro h
  have h1 : W64 1 ∈ GMap.listToSet membersW := by rw [GMap.elem_of_list_to_set]; decide
  rw [h] at h1
  exact GMap.not_elem_of_empty _ h1

theorem three_memW : W64 3 ∈ GMap.listToSet membersW := by
  rw [GMap.elem_of_list_to_set]; decide

theorem three_nmemW : W64 3 ∉ GMap.listToSet votersW := by
  rw [GMap.elem_of_list_to_set]; decide

theorem zero_nmemW : W64 0 ∉ GMap.listToSet votersW := by
  rw [GMap.elem_of_list_to_set]; decide

/-- The configuration `StartClusterWitness` starts node `id` with, on the storage `st`: as
`StartCluster`'s, with check-quorum on (what makes a leader replace an unresponsive voter by the
witness). -/
abbrev nodeConfigW (id : w64) (st : Loc) : Config :=
  { ID' := id, ElectionTick' := W64 10, HeartbeatTick' := W64 1,
    Storage' := interface.mkOk (go.GoType.PointerType rStorageTy) #st,
    Applied' := 0, AsyncStorageWrites' := false, MaxSizePerMsg' := W64 1048576,
    MaxCommittedSizePerReady' := 0, MaxUncommittedEntriesSize' := 0,
    MaxInflightMsgs' := W64 256, MaxInflightBytes' := 0, CheckQuorum' := true,
    PreVote' := false, ReadOnlyOption' := 0,
    Logger' := interface.mkOk qLoggerTy #qLoggerV,
    DisableProposalForwarding' := false, DisableConfChangeValidation' := false,
    StepDownOnRemoval' := true, TraceLogger' := GoInterface.nil }

theorem nodeConfigW_valid (id : w64) (st : Loc) (h : id ∈ votersW) :
    ConfigValid (nodeConfigW id st) := by
  simp only [votersW, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold ConfigValid
  rcases h with rfl | rfl <;> simp <;> decide

section reg
variable [KVStor GF]

/-- What `StartClusterWitness` holds of a replica between starting its node and starting its
replica: as `StartCluster`'s `drvRes`, the node in the static mode of a cluster that admits no conf
change (`KVCCS`). -/
def drvResW (γr : RKVNames) (bud : BudgetNames) (id : w64) (nd : GoInterface) (st : Loc) :
    IProp GF :=
  iprop(∃ (γn : NodeNames) (n : Loc),
    ⌜γn.raft = γr.raft ∧ γn.bud = bud ∧ γn.stor = kvStorIface st ∧
      nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
    nodeDriver γn id n [] ∗ (∃ (ms : Loc) (γs : MemStorNames), kvStorRec st ms γs) ∗
    id ↪[γr.seq] W64 0 ∗
    ⌜KVCCS γn⌝ ∗ nodeCfg γn 0 (cfgState (GMap.listToSet membersW) ∅))

theorem StartClusterWitness.wp_proof
    (wp_copyIDs : kvwitness.copyIDs.spec (GF := GF) (hG := hG))
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG))
    (wp_InitialState : kvwitness.Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : kvwitness.Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_newKV : kvwitness.newKV.spec (GF := GF) (hG := hG))
    (wp_deliver : kvwitness.deliver.spec (GF := GF) (hG := hG))
    (wp_tick : kvwitness.tick.spec (GF := GF) (hG := hG))
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG))
    (wp_RestartNode : RestartNode.spec (GF := GF) (hG := hG))
    (wp_NewWitnessStore : kvwitness.NewWitnessStore.spec (GF := GF) (hG := hG))
    (wp_GetWitnessState : kvwitness.WitnessStore.GetWitnessState.spec (GF := GF) (hG := hG))
    (wp_WClose : kvwitness.WitnessStore.Close.spec (GF := GF) (hG := hG))
    (wp_GetState : kvwitness.witnessRead.GetState.spec (GF := GF) (hG := hG))
    (wp_Update : kvwitness.witnessRead.Update.spec (GF := GF) (hG := hG))
    (wp_NewWitness : NewWitness.spec (GF := GF) (hG := hG)) :
    StartClusterWitness.spec (GF := GF) (hG := hG) := by
  intro vsl Hrb
  wp_start as ⟨#HstorInv, #Hvsl⟩
  rw [show ([W64 1, W64 2] : List w64) = votersW from rfl]
  ihave %Hvlen := ownSlice_len _ _ _ $$ Hvsl
  have Hvlen2 : sint.Z vsl.len = 2 := by
    have h := Hvlen.1
    simp only [votersW, List.length_cons, List.length_nil] at h
    word
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  -- `members := append(copyIDs(voters), witness)`, read-only from here on
  wp_apply wp_copyIDs vsl votersW DFrac.discard $$ [$Hvsl] as %c ⟨-, Hc, Hccap⟩
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sl3 ⟨Hsl3, -⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hc $Hccap $Hsl3] as %msl ⟨Hmsl, -, -⟩
  rw [show votersW ++ [W64 3] = membersW from rfl]
  imod ownSlice_persist _ _ _ $$ Hmsl with #Hmsl
  try wp_auto
  wp_apply wp_map_make1 (K := w64) (V := GoInterface) as %mP HmP
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mS HmS
  -- raft's ghost state for the members `1, 2, 3` in the static mode, at the witness `3`, which no
  -- node runs at; the cluster admits no conf change (`ccOk` false), out of the no-snapshot mode;
  -- with the store's invariant from the client's share, as `StartCluster`'s
  imod ownRaftGhost_alloc_core (GF := GF) ⊤ (GMap.listToSet membersW) (GMap.listToSet votersW)
      none (fun _ _ => False) [] (W64 0)
      (fun γ => iprop(∃ γr : RKVNames, ⌜γr.raft = γ⌝ ∗ rkvInv γr ∗ rkvVal γr kvEmpty ∗
        ([∗map] id ↦ s ∈ constMap votersW (W64 0), id ↪[γr.seq] s)))
      none (fun _ h => by cases h) false (fun h => by cases h) (W64 3)
      ⟨three_nmemW, .inr ⟨three_memW, rfl⟩⟩ membersW_ne zero_nmemW (BootWf_nil _)
      (fun h => absurd rfl h) (.inl rfl) $$ []
    with ⟨%γ, %Hγ, #Hcinv, #Hc0, Hghosts, ⟨%γr, %Hγr, #Hreg, Hval, Hseqs⟩, -, ⟨%Hwit, Hwg⟩⟩
  · unfold allocClientGen
    iintro %γ0 %_ #_ HcL Hfresh HrdF
    imod rkvInv_alloc (GF := GF) ⊤ γ0 (constMap votersW (W64 0)) $$ HcL Hfresh HrdF
      with ⟨%γr0, %Hγr0, #Hreg0, Hval0, Hseqs0⟩
    ihave #Hnoop := kv_noopAu γr0 $$ Hreg0
    subst Hγr0
    imodintro
    iframe Hnoop
    iexists γr0
    iframe Hreg0 Hval0 Hseqs0
    ipureintro; rfl
  obtain ⟨Hcfg, Hdyn, HccOk, -, -, HnsR⟩ := Hγ
  -- the witness's first state, a lower bound of its history
  icases wGhost_read γ wInit $$ Hwg with ⟨Hwg, #Hwst0⟩
  -- the term budget
  imod budget_alloc (GF := GF) Hrb ⊤ with ⟨%bud, #Hbinv, #Hlb0⟩
  rw [listToSet_constMap]
  simp only [Option.isSome_none]
  ihave Hghosts := bigSepM_constMap votersW () votersW_nodup
    (fun id _ => ownRaftGhost (GF := GF) γ id (initPStateAt (W64 0) []) false) $$ Hghosts
  ihave Hseqs := bigSepM_constMap votersW (W64 0) votersW_nodup
    (fun id s => (id ↪[γr.seq] s : IProp GF)) $$ Hseqs
  subst Hγr
  ihave Htodo := (BigSepL.bigSepL_sep_eqv
    (Φ := fun _ id => ownRaftGhost (GF := GF) γr.raft id (initPStateAt (W64 0) []) false)
    (Ψ := fun _ id => (id ↪[γr.seq] W64 0 : IProp GF)) (l := votersW)).2 $$ [Hghosts Hseqs]
  · iframe Hghosts Hseqs
  -- the nodes
  ihave IH1 : iprop(∃ (k : w64) (idv : w64) (M : GMap w64 GoInterface) (S : GMap w64 Loc),
      "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "HmP" ∷ mP ↦$ M ∗ "HmS" ∷ mS ↦$ S ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 2⌝ ∗
      "#Hpeers" ∷ ([∗map] id ↦ nd ∈ M, peerOk γr.raft bud id nd) ∗
      "Hdone" ∷ ([∗list] id ∈ votersW.take (sint.nat k), ∃ (nd : GoInterface) (st : Loc),
        ⌜M !! id = some nd ∧ S !! id = some st⌝ ∗ drvResW γr bud id nd st) ∗
      "Htodo" ∷ ([∗list] id ∈ votersW.drop (sint.nat k),
        ownRaftGhost γr.raft id (initPStateAt (W64 0) []) false ∗ id ↪[γr.seq] W64 0) ∗
      "%Hdom" ∷ ⌜∀ id, id ∈ votersW.drop (sint.nat k) → M !! id = none ∧ S !! id = none⌝)
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
  · have Hlt : sint.Z k < 2 := by word
    have Hlt' : sint.nat k < votersW.length := by simp [votersW]; word
    obtain ⟨id0, Hid0⟩ : ∃ id0, votersW[sint.nat k]? = some id0 :=
      ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z vsl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z k) _ DFrac.discard id0 Hk.1 $$ [Hvsl] as -
    · iframe Hvsl; ipureintro; exact Hid0
    -- `st := &Storage{MemoryStorage: raft.NewMemoryStorage(), voters: members, witness: witness}`
    wp_apply wp_NewMemoryStorage (2 ^ 64) (by simp only [memStorEmpty]; word)
      as %ms %γs ⟨-, Hmem, -⟩
    -- `st`, registered
    iStructNamed «$r0»
    imod kvStor_register «$r0_ptr» ms γs ⊤ CoPset.subseteq_top $$ HstorInv MemoryStorage with #Hrec
    ipersist voters
    ipersist witness
    have Hid0m : id0 ∈ votersW := List.mem_of_getElem? Hid0
    have Hid0M : id0 ∈ membersW := by
      simp only [votersW, List.mem_cons, List.not_mem_nil, or_false] at Hid0m
      rcases Hid0m with rfl | rfl <;> decide
    rw [drop_cons_of_getElem? _ _ _ Hid0]
    icases Htodo with ⟨⟨Hghost, Hseq⟩, Htodo⟩
    ihave #Hlogger := qLogger_isLogger wp_Debugf wp_Errorf wp_Infof wp_Warningf
    ihave #Hstor := kvStorage_isStorage wp_Snapshot «$r0_ptr» ms γs $$ Hpkg Hrec
    ihave #Hinit := kvStorage_initialState wp_InitialState «$r0_ptr» _ membersW memStorEmpty
      (W64 3) $$ Hpkg voters Hmsl witness
    have Hiface : kvStorIface «$r0_ptr» =
        GoInterface.ok ⟨go.GoType.PointerType rStorageTy, #«$r0_ptr»⟩ := rfl
    rw [Hiface]
    ihave Hown : kvOwnStorage (interface.ok ⟨go.GoType.PointerType rStorageTy, #«$r0_ptr»⟩)
        memStorEmpty $$ [Hmem]
    · unfold kvOwnStorage
      iexists «$r0_ptr», ms, γs
      iframe Hrec Hmem
      ipureintro; rfl
    ihave Hown : ownStorage (interface.ok ⟨go.GoType.PointerType rStorageTy, #«$r0_ptr»⟩)
        memStorEmpty $$ Hown
    ihave Hghost : rnInit γr.raft .static id0 (GMap.listToSet membersW) $$ [Hghost]
    · unfold rnInit
      rw [← initPState_eq]
      iexact Hghost
    wp_apply (wp_RestartNode γr.raft .static bud _ (nodeConfigW id0 «$r0_ptr») qLogger
      ⟨go.GoType.PointerType rStorageTy, #«$r0_ptr»⟩ memStorEmpty
      (HardStateM.mk (W64 0) (W64 0) (W64 0)) (kvwitness.kvConfState membersW (W64 3))
      (nodeConfigW_valid id0 «$r0_ptr» Hid0m) rfl rfl
      (by show sint.Z (W64 256) < 2 ^ 62; decide) rfl rfl rfl
      (by right; show W64 1048576 ≠ W64 0; decide)
      rfl (fun h => by cases h) rfl rfl rfl (by left; rfl) rfl ⟨rfl, rfl, rfl⟩
      (by decide) membersW_nodup (by decide) (by decide) rfl rfl rfl rfl Hcfg Hid0M
      (fun h => by cases h) rfl (.inr ⟨by decide, Hwit.symm, rfl⟩))
      $$ [$Hraftinit $«$a0» $Hlogger $Hstor $Hown $Hinit $Hghost $Hc0 $Hbinv $Hlb0]
      as %nd ⟨%γn, %n, %Hnd, #HisNode, Hdrv, Hncfg⟩
    obtain ⟨Hr, Hb, Hs, Hmd, rfl⟩ := Hnd
    have Hdrop := drop_cons_of_getElem? _ _ _ Hid0
    have Hnd' : (votersW.drop (sint.nat k)).Nodup := votersW_nodup.sublist (List.drop_sublist _ _)
    rw [Hdrop] at Hnd'
    have Hid0n : id0 ∉ votersW.drop (sint.nat k + 1) := (List.nodup_cons.mp Hnd').1
    obtain ⟨HM0, HS0⟩ := Hdom id0 (by rw [Hdrop]; exact List.mem_cons_self)
    wp_apply wp_mapInsert go.uint64 mP M id0 _ $$ [$HmP] as HmP
    wp_apply wp_mapInsert go.uint64 mS S id0 «$r0_ptr» $$ [$HmS] as HmS
    wp_for_post
    iframe
    iexists k + W64 1, id0, <[id0 := interface.mkOk (go.GoType.PointerType node.ty) #n]> M,
      <[id0 := «$r0_ptr»]> S
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
            (<[id0 := «$r0_ptr»]> S) !! id = some st'⌝ ∗ drvResW (GF := GF) γr bud id nd st'))).2
      isplitl [Hdone]
      · iapply (BigSepL.bigSepL_mono (Φ := fun _ id => iprop(∃ (nd : GoInterface) (st' : Loc),
            ⌜M !! id = some nd ∧ S !! id = some st'⌝ ∗ drvResW (GF := GF) γr bud id nd st')) ?_)
          $$ Hdone
        intro j x Hx
        have Hxt : x ∈ votersW.take (sint.nat k) := List.mem_of_getElem? Hx
        have Hne : x ≠ id0 := take_drop_ne votersW votersW_nodup (sint.nat k) x id0 Hxt
          (by rw [Hdrop]; exact List.mem_cons_self)
        iintro ⟨%nd, %st', %Hl, Hres⟩
        iexists nd, st'
        iframe Hres
        ipureintro
        rw [GMap.lookup_insert_ne _ _ (Ne.symm Hne), GMap.lookup_insert_ne _ _ (Ne.symm Hne)]
        exact Hl
      · iapply (BigSepL.bigSepL_singleton (Φ := fun _ id => iprop(∃ (nd : GoInterface) (st' : Loc),
          ⌜(<[id0 := interface.mkOk (go.GoType.PointerType node.ty) #n]> M) !! id = some nd ∧
            (<[id0 := «$r0_ptr»]> S) !! id = some st'⌝ ∗ drvResW (GF := GF) γr bud id nd st'))).2
        iexists _, «$r0_ptr»
        isplitr
        · ipureintro; exact ⟨GMap.lookup_insert _ _ _, GMap.lookup_insert _ _ _⟩
        unfold drvResW
        iexists γn, n
        iframe Hdrv Hseq Hncfg
        isplitr
        · ipureintro; exact ⟨Hr, Hb, by rw [Hs]; rfl, rfl⟩
        isplitr
        · iexists ms, γs
          iframe Hrec
        ipureintro
        exact ⟨Hmd, by rw [Hr, HccOk]; intro _ _ h; exact h, by rw [Hr]; exact HnsR⟩
    ipureintro
    intro id Hid
    have Hne : id ≠ id0 := fun h => Hid0n (h ▸ Hid)
    rw [GMap.lookup_insert_ne _ _ (Ne.symm Hne), GMap.lookup_insert_ne _ _ (Ne.symm Hne)]
    exact Hdom id (by rw [Hdrop]; exact List.mem_cons_of_mem _ Hid)
  · have Hk2 : sint.nat k = 2 := by word
    rw [Hk2]
    simp only [show votersW.take 2 = votersW from rfl, show votersW.drop 2 = [] from rfl]
    clear Hdom
    imod ownMap_persist mP _ M $$ HmP with #HmP
    imod ownMap_persist mS _ S $$ HmS with #HmS
    ipersist peers
    ipersist storages
    ipersist witness
    -- the transport's transfer budget: `timeouts` under its lock
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
    ipersist send
    -- `ws := NewWitnessStore()`: the store's states the witness's protocol history and the budget
    ihave #Herr := wErrOk_of_init (GF := GF) $$ Hraftinit
    wp_apply (wp_NewWitnessStore (fun σ => iprop(wGhost γr.raft σ.ws ∗ termLB bud σ.term)))
      $$ [$Herr Hwg] as %ws #Hws
    · rw [WHS.zero_ws]
      iframe Hwg
      iExactEq Hlb0
      rfl
    ihave #Hwsi := kvWStore_isWitnessStorage wp_GetWitnessState wp_WClose wp_GetState wp_Update ws
      kvWitN (fun σ => iprop(wGhost γr.raft σ.ws ∗ termLB bud σ.term)) $$ Hpkg Hws
    try wp_auto
    ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
    ihave Hncap := ownSliceCap_nil (V := Loc) (GF := GF)
    ihave IH2 : iprop(∃ (k : w64) (idv : w64) (ksl : GoSlice) (rs : List Loc),
        "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "kvs" ∷ kvs_ptr ↦ ksl ∗
        "Hks" ∷ ksl ↦* rs ∗ "Hkcap" ∷ ownSliceCap Loc ksl (DFrac.own 1) ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 2⌝ ∗ "%Hrs" ∷ ⌜rs.length = sint.nat k⌝ ∗
        "#Hregs" ∷ ([∗list] r ∈ rs, ∃ γp, isKV γr γp r) ∗
        "Hdrv" ∷ ([∗list] id ∈ votersW.drop (sint.nat k), ∃ (nd : GoInterface) (st : Loc),
          ⌜M !! id = some nd ∧ S !! id = some st⌝ ∗ drvResW γr bud id nd st))
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
    · have Hlt : sint.Z k < 2 := by word
      have Hlt' : sint.nat k < votersW.length := by simp [votersW]; word
      obtain ⟨id0, Hid0⟩ : ∃ id0, votersW[sint.nat k]? = some id0 :=
        ⟨_, List.getElem?_eq_getElem Hlt'⟩
      have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z vsl.len := ⟨Hk.1, by word⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z k) _ DFrac.discard id0 Hk.1 $$ [Hvsl] as -
      · iframe Hvsl; ipureintro; exact Hid0
      have Hid0m : id0 ∈ votersW := List.mem_of_getElem? Hid0
      have Hid0w : id0 ≠ W64 3 := by
        simp only [votersW, List.mem_cons, List.not_mem_nil, _root_.or_false] at Hid0m
        rcases Hid0m with rfl | rfl <;> decide
      have Hid00 : id0 ≠ W64 0 := by
        simp only [votersW, List.mem_cons, List.not_mem_nil, _root_.or_false] at Hid0m
        rcases Hid0m with rfl | rfl <;> decide
      have Hdrop := drop_cons_of_getElem? _ _ _ Hid0
      rw [Hdrop]
      icases Hdrv with ⟨⟨%nd, %st, %Hlk, Hres⟩, Hdrv⟩
      obtain ⟨HMl, HSl⟩ := Hlk
      unfold drvResW
      icases Hres with ⟨%γn, %n, %Hgn, Hnode, #Hsrec, Hseq, %Hmd, Hncfg⟩
      obtain ⟨Hr, Hb, Hs, rfl⟩ := Hgn
      try wp_auto
      -- `w := raft.NewWitness(raft.WitnessConfig{ID: witness, Storage: ws, CheckQuorum: true})`
      wp_apply wp_NewWitness as %w Hw
      simp only
      ihave Hwi : ownWitnessIT (GF := GF) γr.raft kvWitN (termLB bud)
          (interface.mkOk (go.GoType.PointerType witness.ty) #w) $$ [Hw]
      · ihave #Hwst0' : wSt (GF := GF) γr.raft WHS.zero.ws $$ []
        · rw [WHS.zero_ws]; iexact Hwst0
        ihave #Hlb0' : termLB (GF := GF) bud WHS.zero.term $$ []
        · iExactEq Hlb0; rfl
        iapply ownWitnessIT_intro γr.raft kvWitN (termLB bud) w _ true false WHS.zero true
          $$ [Hw] Hwsi Hwst0' Hlb0'
        rw [Hwit]; unfold kvWStoreIface; iexact Hw
      try wp_auto
      wp_apply wp_map_lookup1 go.uint64 _ mP M id0 DFrac.discard $$ HmP as -
      wp_apply wp_map_lookup1 go.uint64 _ mS S id0 DFrac.discard $$ HmS as -
      simp only [HMl, HSl, Option.getD_some]
      try wp_auto
      wp_apply (wp_newKV γr γn id0 n st _ (ccV2Of (.v1 (rmCC (W64 3))))
          (cfgState (GMap.listToSet membersW) ∅) (cfgState (GMap.listToSet membersW) ∅)
          (interface.mkOk (go.GoType.PointerType witness.ty) #w))
          $$ [Hnode Hseq Hncfg Hwi]
      · iframe Hreg Hnode Hsrec Hc0 Hseq Hncfg
        isplitr
        · ipureintro; exact Hr
        isplitr
        · ipureintro; exact .inr Hmd
        isplitr
        · ipureintro; exact Hs
        isplitr
        · unfold sendSpec
          imodintro
          iintro %msl' %ms %Φ'
          imodintro
          iintro ⟨Hmsl', Hmsok, Hcr, Htks⟩ HΦ'
          rw [Hr, Hb]
          wp_auto
          wp_apply (wp_deliver γr.raft bud mP «$r0_ptr» M msl' ms)
            $$ [$Hmsl' $Hmsok $Hcr $Htks]
          · iframe #
          iapply HΦ'
          itrivial
        unfold kvWitRes
        iright
        rw [Hr, Hb]
        iframe Hwi
        ipureintro
        refine ⟨Hmd.1, by rw [Hwit]; decide, by rw [Hwit]; exact Hid0w, Hid00⟩
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
    · have Hk2' : sint.nat k = 2 := by word
      iapply HΦ
      iexists γr, rs
      iframe Hks Hval Hregs
      ipureintro; rw [Hrs, Hk2']

end reg

end proof

end kvwitness
end EtcdGrove
end Perennial
