/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/StartCluster.lean`. Lean-first (no
Rocq counterpart).

The cluster bring-up of the register's `Main` (until 2026-10-19), at any storage registry
(`[KVStor GF]`): raft's ghost state for the voters `1, 2, 3` (2026-10-21, D22 S-r: in the static
mode, admitting no configuration change, `ownRaftGhost_alloc_snap`; from stage N until then in the
dynamic mode of the cluster's one change, `RemoveMember(3)`) with the
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

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.StartCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.NewStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__InitialState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.tick
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.quietLogger__Debugf
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.quietLogger__Errorf
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.quietLogger__Infof
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.quietLogger__Warningf
public import Spec.go_etcd_io.raft.v3.RestartNode
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KVStorageInstance
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Alloc
public import Proof.go_etcd_io.raft.v3.Linked

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open RaftLink
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- `quietLogger{}` is a raft `Logger`. -/
theorem qLogger_isLogger
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG)) :
    ⊢ isLogger (GF := GF) qLogger := by
  unfold isLogger
  iintro %meth %Hmeth %format %args
  simp only [logMethods, List.mem_cons, List.not_mem_nil, or_false] at Hmeth
  rcases Hmeth with rfl | rfl | rfl | rfl
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Infof format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Debugf format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Warningf format args) $$ [] HΦ
    itrivial
  · dsimp only [qLogger, interface.mk]
    imodintro
    iintro %Φ - HΦ
    iapply (wp_Errorf format args) $$ [] HΦ
    itrivial

/-- The map of the keys `l`, each to `v` (`GMap.listToSet l` for `v = ()`). -/
def constMap {V : Type} (l : List w64) (v : V) : GMap w64 V :=
  match l with
  | [] => ∅
  | k :: l => GMap.insert k v (constMap l v)

theorem constMap_lookup_none {V : Type} (l : List w64) (v : V) (k : w64) (h : k ∉ l) :
    constMap l v !! k = none := by
  induction l with
  | nil => rfl
  | cons k' l IH =>
    simp only [List.mem_cons, not_or] at h
    show (GMap.insert k' v (constMap l v)) !! k = none
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h.1)]
    exact IH h.2

theorem listToSet_constMap (l : List w64) : GMap.listToSet l = constMap l () := by
  induction l with
  | nil => rfl
  | cons k l IH => show GMap.insert k () (GMap.listToSet l) = _; rw [IH]; rfl

/-- A big separating conjunction over a `constMap` is one over its list. -/
theorem bigSepM_constMap {V : Type} (l : List w64) (v : V) (hnd : l.Nodup)
    (Φ : w64 → V → IProp GF) :
    ([∗map] k ↦ x ∈ constMap l v, Φ k x) ⊢ [∗list] k ∈ l, Φ k v := by
  induction l with
  | nil => iintro -; iapply (BigSepL.bigSepL_nil (Φ := fun _ k => Φ k v)).2; iempintro
  | cons k l IH =>
    have hk : k ∉ l := (List.nodup_cons.mp hnd).1
    rw [show constMap (k :: l) v = GMap.insert k v (constMap l v) from rfl]
    iintro H
    ihave ⟨H1, H2⟩ := (BigSepM.bigSepM_insert (Φ := Φ) (m := constMap l v) (i := k) (x := v)
      (constMap_lookup_none l v k hk)).1 $$ H
    iapply (BigSepL.bigSepL_cons (Φ := fun _ k => Φ k v)).2
    iframe H1
    iapply IH (List.nodup_cons.mp hnd).2 $$ H2

/-- The cluster's voters. -/
def clusterIds : List w64 := [W64 1, W64 2, W64 3]

theorem clusterIds_nodup : clusterIds.Nodup := by decide

theorem constMap_lookup_isSome {V : Type} (l : List w64) (v : V) (k : w64) :
    (constMap l v !! k).isSome ↔ k ∈ l := by
  induction l with
  | nil =>
    simp only [List.not_mem_nil, iff_false]
    rw [show ((constMap [] v : GMap w64 V) !! k) = none from rfl]
    simp
  | cons k' l IH =>
    show (GMap.insert k' v (constMap l v) !! k).isSome ↔ _
    by_cases h : k' = k
    · subst h; rw [GMap.lookup_insert_eq]; simp
    · rw [GMap.lookup_insert_ne _ _ h, IH]
      simp [List.mem_cons, Ne.symm h]

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

/-! ## The cluster's mode (2026-10-21, D22 S-r): static, no configuration change

(From stage N, 2026-10-15, until D22 S-r the dynamic mode of `RemoveMember(3)`.) -/

/-- The conf-change bytes the cluster admits: none. -/
def ccOkS (_ty : w32) (_bs : List w8) : Prop := False

/-- A replica's node, in the cluster's static mode, taking snapshots of the cluster's data
(D22 S-r). -/
theorem kvStat_cluster (γn : NodeNames) (Hok : γn.raft.reCCOk = ccOkS) (Hmd : γn.mode = .static)
    (Hns : γn.raft.reNoXfer = false) (Hsn : γn.snapIn = true)
    (Hsok : γn.raft.reSnapOkRaw = kvSnapOk) (Hdyn : γn.raft.reDyn = none)
    (Htrk : γn.raft.reTracked = none) : KVStat γn :=
  ⟨Hmd, fun ty bs h => by rw [Hok] at h; exact h, Hns, Hsn, Hsok, Hdyn, Htrk⟩

theorem take_drop_ne (l : List w64) (hnd : l.Nodup) (n : Nat) (x y : w64)
    (hx : x ∈ l.take n) (hy : y ∈ l.drop n) : x ≠ y := by
  rw [← List.take_append_drop n l, List.nodup_append] at hnd
  exact hnd.2.2 x hx y hy

theorem drop_cons_of_getElem? (l : List w64) (n : Nat) (x : w64) (h : l[n]? = some x) :
    l.drop n = x :: l.drop (n + 1) := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.drop_eq_getElem_cons hn]
  rw [List.getElem?_eq_getElem hn] at h
  rw [Option.some.inj h]

theorem take_succ_of_getElem? (l : List w64) (n : Nat) (x : w64) (h : l[n]? = some x) :
    l.take (n + 1) = l.take n ++ [x] := by
  rw [List.take_add_one, h]; rfl

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
    nodeDriver γn id n [] hsZero ∗ (∃ (ms : Loc) (γs : MemStorNames), kvStorRec st ms γs) ∗
    id ↪[γr.seq] W64 0 ∗
    -- (D22 S-r) the storage's snapshot token, for `run`
    runStor γr st memStorEmpty ∗
    -- (2026-10-15, stage N; static since D22 S-r) the node's mode and the driver's view of its
    -- configuration
    ⌜KVStat γn⌝ ∗ nodeCfg γn 0 (cfgState (GMap.listToSet clusterIds) ∅))

theorem StartCluster.wp_proof
    (wp_NewStorage : kv.NewStorage.spec (GF := GF) (hG := hG))
    (wp_InitialState : kv.Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : kv.Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_New : kv.New.spec (GF := GF) (hG := hG))
    (wp_deliver : kv.deliver.spec (GF := GF) (hG := hG))
    (wp_tick : kv.tick.spec (GF := GF) (hG := hG))
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
  -- (2026-10-21, D22 S-r) in the static mode, admitting no conf change (until then
  -- `raft_dyn_alloc`, the dynamic mode of `RemoveMember(3)`)
  imod ownRaftGhost_alloc_snap (GF := GF) ⊤ (GMap.listToSet clusterIds) (GMap.listToSet clusterIds)
    ccOkS kvSnapOk
    (fun γ => iprop(∃ γr : RKVNames, ⌜γr.raft = γ⌝ ∗ rkvInv γr ∗ rkvVal γr kvEmpty ∗
      ([∗map] id ↦ s ∈ constMap clusterIds (W64 0), id ↪[γr.seq] s)))
    clusterIds_ne (by rw [GMap.elem_of_list_to_set]; decide) $$ []
    with ⟨%γ, %Hcfg', #Hcinv, #Hc0, Hghosts, ⟨%γr, %Hγr, #Hreg, Hval, Hseqs⟩,
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
  have Hcfg : γ.reCfg = GMap.listToSet clusterIds := Hcfg'.1
  -- (2026-10-19, D22 S-a) leader transfer on (`RaftNames.reNoXfer`)
  have Hnx := Hcfg'.2.2.2.1
  have HccOk := Hcfg'.2.2.1
  -- (D22 S-r) snapshots on, of the cluster's data (`kvSnapOk`)
  have HnoSnap := Hcfg'.2.2.2.2.1
  have Hsok := Hcfg'.2.2.2.2.2.2.1
  -- (2026-10-26, D22 J2) no snapshot directory
  have HsLoc := Hcfg'.2.2.2.2.2.2.2
  have Hdyn := Hcfg'.2.1
  have Htrk := Hcfg'.2.2.2.2.2.1
  -- the term budget (D19b: backed by time receipts; the ticks' credits are the ticking loops'
  -- own receipts)
  imod budget_alloc (GF := GF) Hrb ⊤ with ⟨%bud, #Hbinv, #Hlb0⟩
  rw [listToSet_constMap]
  ihave Hghosts := bigSepM_constMap clusterIds () clusterIds_nodup
    (fun id _ => ownRaftGhost (GF := GF) γ id initPState) $$ Hghosts
  ihave Hseqs := bigSepM_constMap clusterIds (W64 0) clusterIds_nodup
    (fun id s => (id ↪[γr.seq] s : IProp GF)) $$ Hseqs
  subst Hγr
  ihave Htodo := (BigSepL.bigSepL_sep_eqv
    (Φ := fun _ id => ownRaftGhost (GF := GF) γr.raft id initPState)
    (Ψ := fun _ id => (id ↪[γr.seq] W64 0 : IProp GF)) (l := clusterIds)).2 $$ [Hghosts Hseqs]
  · iframe Hghosts Hseqs
  -- the nodes
  ihave IH1 : iprop(∃ (k : w64) (idv : w64) (M : GMap w64 GoInterface) (S : GMap w64 Loc),
      "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "HmP" ∷ mP ↦$ M ∗ "HmS" ∷ mS ↦$ S ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 3⌝ ∗
      "#Hpeers" ∷ ([∗map] id ↦ nd ∈ M, kvPeerOk γr.raft bud id nd) ∗
      "Hdone" ∷ ([∗list] id ∈ clusterIds.take (sint.nat k), ∃ (nd : GoInterface) (st : Loc),
        ⌜M !! id = some nd ∧ S !! id = some st⌝ ∗ drvRes γr bud id nd st) ∗
      "Htodo" ∷ ([∗list] id ∈ clusterIds.drop (sint.nat k),
        ownRaftGhost γr.raft id initPState ∗ id ↪[γr.seq] W64 0) ∗
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
    wp_apply (wp_NewStorage _ clusterIds) $$ [$HstorInv $Hvsl]
      as %st ⟨%ms, %γs, #Hrec, #Hvoters, Hmem, Hca, Hstok, %Hcap⟩
    -- (D22 S-b′3) the storage's certificate registry tied to raft's names
    imod memCertInv_alloc γr.raft γs ⊤ $$ Hca with #Hci
    ihave #Hcl : certLink (GF := GF) γr.raft (kvStorIface st) $$ []
    · iunfold certLink; iright; iapply kvStorCertOk_intro γr.raft st ms γs $$ Hci Hrec
    have Hid0m : id0 ∈ clusterIds := List.mem_of_getElem? Hid0
    rw [drop_cons_of_getElem? _ _ _ Hid0]
    icases Htodo with ⟨⟨Hghost, Hseq⟩, Htodo⟩
    ihave #Hlogger := qLogger_isLogger wp_Debugf wp_Errorf wp_Infof wp_Warningf
    ihave #Hstor := kvStorage_isStorage wp_Snapshot st ms γs $$ Hpkg Hrec
    ihave #Hinit := kvStorage_initialState wp_InitialState st _ clusterIds memStorEmpty
      $$ Hpkg Hvoters Hvsl
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
    -- (2026-10-19, D21 M2r) leader transfer on: (D22 S-a) the allocation's
    -- (`RaftNames.reNoXfer`, until then out of the no-snapshot mode: nothing committed)
    have HnsR : γr.raft.reNoXfer = false := Hnx
    ihave Hghost : rnInit γr.raft .static id0 (GMap.listToSet clusterIds) $$ [Hghost]
    · iunfold rnInit
      iexact Hghost
    wp_apply (wp_RestartNode γr.raft .static
      bud _ (nodeConfig id0 st) qLogger
      ⟨go.GoType.PointerType rStorageTy, #st⟩ memStorEmpty (HardStateM.mk (W64 0) (W64 0) (W64 0))
      (kv.kvConfState clusterIds) true
      (nodeConfig_valid id0 st Hid0m) rfl rfl
      (by show sint.Z (W64 256) < 2 ^ 62; decide) rfl rfl rfl
      (by right; show W64 1048576 ≠ W64 0; decide)
      rfl rfl rfl rfl (by left; rfl) rfl ⟨rfl, rfl, rfl⟩
      (by decide) clusterIds_nodup (by decide) (by decide) rfl rfl rfl rfl Hcfg Hid0m
      rfl (fun _ => ⟨HnoSnap, rfl⟩))
      $$ [$Hraftinit $«$a0» $Hlogger $Hstor $Hown $Hinit $Hghost $Hc0 $Hbinv $Hlb0 $Hcl]
      as %nd ⟨%γn, %n, %Hnd, #HisNode, Hdrv, Hncfg⟩
    obtain ⟨Hr, Hb, Hs, Hmd, Hsn, rfl⟩ := Hnd
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
    · iapply (BigSepM.bigSepM_insert (Φ := fun id nd => kvPeerOk (GF := GF) γr.raft bud id nd)
        HM0).2
      iframe Hpeers
      unfold kvPeerOk
      iexists γn, n
      iframe HisNode
      ipureintro; exact ⟨Hr, Hb, rfl, Hsn, by rw [Hr, HsLoc]⟩
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
        isplitl [Hstok]
        · unfold runStor
          iexists ms, γs, vsl, clusterIds
          iframe Hrec Hstok Hci Hvoters Hvsl
          ipureintro
          exact ⟨Hcap, by rw [Hcfg], clusterIds_nodup, by decide, by decide, by decide,
            Int.le_refl _⟩
        ipureintro
        exact kvStat_cluster γn (by rw [Hr]; exact HccOk) Hmd (by rw [Hr]; exact HnsR) Hsn
          (by rw [Hr]; exact Hsok) (by rw [Hr]; exact Hdyn) (by rw [Hr]; exact Htrk)
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
      icases Hres with ⟨%γn, %n, %Hgn, Hnode, #Hsrec, Hseq, Hrs, %Hmd, Hncfg⟩
      obtain ⟨Hr, Hb, Hs, rfl⟩ := Hgn
      wp_apply wp_map_lookup1 go.uint64 _ mP M id0 DFrac.discard $$ HmP as -
      wp_apply wp_map_lookup1 go.uint64 _ mS S id0 DFrac.discard $$ HmS as -
      simp only [HMl, HSl, Option.getD_some]
      wp_apply (wp_New γr γn id0 n st _ (cfgState (GMap.listToSet clusterIds) ∅))
          $$ [Hnode Hseq Hncfg Hrs]
      · iframe Hreg Hnode Hsrec Hc0 Hseq Hncfg Hrs
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
        wp_apply (wp_deliver γr.raft _ bud mP «$r0_ptr» M msl ms)
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
      ihave #Hpeer := BigSepM.bigSepM_lookup (Φ := fun id nd => kvPeerOk (GF := GF) γr.raft bud id nd)
        HMl $$ Hpeers
      unfold kvPeerOk
      icases Hpeer with ⟨%γn', %n', %Hgn', #HisNode'⟩
      obtain ⟨-, Hb', Hn', -⟩ := Hgn'
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

end kv
end EtcdGrove
end Perennial
