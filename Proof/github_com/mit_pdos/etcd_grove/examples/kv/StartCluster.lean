/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/StartCluster.lean`. Lean-first (no
Rocq counterpart).

The cluster bring-up of the store's `Main`, at any storage registry (`[KVStor GF]`): raft's
static cluster of the voters `1, 2, 3` (2026-10-27: raft's draft API, `Draft.cluster_alloc_static`,
with the term budget; until then `ownRaftGhost_alloc_snap` and `budget_alloc`) with the store's
invariant (`rkvInv_alloc`, which gives the client's half at the empty store), then a first loop over the voters (`NewStorage`, `RestartNode` into `peers` and
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
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KVStorageInstance
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Alloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

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
abbrev clusterIds : List w64 := kvVoters

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

/-- The cluster has a voter. -/
theorem clusterIds_ne : GMap.listToSet clusterIds ≠ ∅ := by
  intro h
  have := clusterIds_size
  rw [h, GMap.size_empty] at this
  omega

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
  simp only [clusterIds, kvVoters, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold ConfigValid
  rcases h with rfl | rfl | rfl <;> simp <;> decide

section reg
variable [KVStor GF]

/-- What `StartCluster` holds of a replica between starting its node and starting its replica: the
node (`Draft.isNode`), its driver token idle on the store's storage, the storage's record, the
replica's sequence-number token, and the storage's snapshot token, for `run`. -/
def drvRes (γr : RKVNames) (id : w64) (nd : GoInterface) (st : Loc) : IProp GF :=
  iprop(∃ (n : Loc), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
    Draft.isNode n γr.cluster kvRaftN id ∗
    Draft.nodeDriver n γr.cluster kvRaftN (Draft.NodeDriverState.init (kvStorIface st)) ∗
    (∃ (ms : Loc) (γs : MemStorNames), kvStorRec st ms γs) ∗
    id ↪[γr.seq] W64 0 ∗ runStor γr st memStorEmpty)

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
    (wp_RestartNode : Draft.RestartNode.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG)) :
    StartCluster.spec (GF := GF) (hG := hG) := by
  intro vsl Hrb
  wp_start as ⟨#HstorInv, #Hvsl⟩
  rw [show ([W64 1, W64 2, W64 3] : List w64) = clusterIds from rfl]
  ihave %Hvlen := ownSlice_len _ _ _ $$ Hvsl
  have Hvlen3 : sint.Z vsl.len = 3 := by
    have h := Hvlen.1
    simp only [clusterIds, kvVoters, List.length_cons, List.length_nil] at h
    word
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := GoInterface) as %mP HmP
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mS HmS
  -- the cluster (the voters `1, 2, 3`, static, of the store's snapshots' data `kvSnapOk`; its
  -- term budget backed by the time receipts), then the store's invariant from the client's share,
  -- with the client's half of the store's state and the sequence-number tokens
  imod Draft.cluster_alloc_static (GF := GF) kvRaftN clusterIds kvSnapOk ⊤ Hrb (by decide)
    clusterIds_nodup (by decide) (by decide)
    with ⟨%γ, Hops, HU, -, #Hstatic, #Hxfer, Hboots⟩
  imod rkvInv_alloc (GF := GF) ⊤ γ (constMap clusterIds (W64 0)) $$ Hops HU
    with ⟨%γr, %Hγr, #Hreg, Hval, Hseqs⟩
  subst Hγr
  ihave Hseqs := bigSepM_constMap clusterIds (W64 0) clusterIds_nodup
    (fun id s => (id ↪[γr.seq] s : IProp GF)) $$ Hseqs
  ihave Htodo := (BigSepL.bigSepL_sep_eqv
    (Φ := fun _ id => Draft.nodeRestartBoot (GF := GF) γr.cluster kvRaftN clusterIds id)
    (Ψ := fun _ id => (id ↪[γr.seq] W64 0 : IProp GF)) (l := clusterIds)).2 $$ [Hboots Hseqs]
  · iframe Hboots Hseqs
  -- the nodes
  ihave IH1 : iprop(∃ (k : w64) (idv : w64) (M : GMap w64 GoInterface) (S : GMap w64 Loc),
      "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "HmP" ∷ mP ↦$ M ∗ "HmS" ∷ mS ↦$ S ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 3⌝ ∗
      "#Hpeers" ∷ ([∗map] id ↦ nd ∈ M, kvPeerOk γr.cluster id nd) ∗
      "Hdone" ∷ ([∗list] id ∈ clusterIds.take (sint.nat k), ∃ (nd : GoInterface) (st : Loc),
        ⌜M !! id = some nd ∧ S !! id = some st⌝ ∗ drvRes γr id nd st) ∗
      "Htodo" ∷ ([∗list] id ∈ clusterIds.drop (sint.nat k),
        Draft.nodeRestartBoot γr.cluster kvRaftN clusterIds id ∗ id ↪[γr.seq] W64 0) ∗
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
    have Hlt' : sint.nat k < clusterIds.length := by simp [clusterIds, kvVoters]; word
    obtain ⟨id0, Hid0⟩ : ∃ id0, clusterIds[sint.nat k]? = some id0 :=
      ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z vsl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z k) _ DFrac.discard id0 Hk.1 $$ [Hvsl] as -
    · iframe Hvsl; ipureintro; exact Hid0
    wp_apply (wp_NewStorage _ clusterIds) $$ [$HstorInv $Hvsl]
      as %st ⟨%ms, %γs, #Hrec, #Hvoters, Hmem, Hca, Hstok, %Hcap⟩
    -- the storage's certificate registry tied to the cluster
    imod Draft.storageCertInv_alloc γr.cluster kvRaftN γs ⊤ $$ Hca with #Hci
    ihave #Hcl := kvStorCertLink_intro γr.cluster kvRaftN st ms γs $$ Hci Hrec
    have Hid0m : id0 ∈ clusterIds := List.mem_of_getElem? Hid0
    rw [drop_cons_of_getElem? _ _ _ Hid0]
    icases Htodo with ⟨⟨Hboot, Hseq⟩, Htodo⟩
    ihave #Hlogger := qLogger_isLogger wp_Debugf wp_Errorf wp_Infof wp_Warningf
    ihave #Hstor := kvStorage_isStorage wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term wp_Entries st
      ms γs $$ Hpkg Hrec
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
    wp_apply (wp_RestartNode γr.cluster kvRaftN clusterIds _ (nodeConfig id0 st) qLogger
      ⟨go.GoType.PointerType rStorageTy, #st⟩ memStorEmpty (HardStateM.mk (W64 0) (W64 0) (W64 0))
      (kv.kvConfState clusterIds)
      (nodeConfig_valid id0 st Hid0m) rfl rfl
      (by show sint.Z (W64 256) < 2 ^ 62; decide) rfl rfl rfl
      (by right; show W64 1048576 ≠ W64 0; decide)
      rfl rfl rfl rfl (by left; rfl) rfl ⟨rfl, rfl, rfl⟩
      rfl rfl rfl rfl rfl Hid0m rfl)
      $$ [$Hraftinit $«$a0» $Hlogger $Hstor $Hown $Hinit $Hboot $Hcl]
      as %nd ⟨%n, %Hnd, #HisNode, Hdrv⟩
    subst Hnd
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
    · iapply (BigSepM.bigSepM_insert (Φ := fun id nd => kvPeerOk (GF := GF) γr.cluster id nd)
        HM0).2
      iframe Hpeers
      unfold kvPeerOk
      iexists n
      iframe HisNode
      ipureintro; rfl
    isplitl
    · iapply (BigSepL.bigSepL_append (Φ := fun _ id => iprop(∃ (nd : GoInterface) (st' : Loc),
          ⌜(<[id0 := interface.mkOk (go.GoType.PointerType node.ty) #n]> M) !! id = some nd ∧
            (<[id0 := st]> S) !! id = some st'⌝ ∗ drvRes (GF := GF) γr id nd st'))).2
      isplitl [Hdone]
      · iapply (BigSepL.bigSepL_mono (Φ := fun _ id => iprop(∃ (nd : GoInterface) (st' : Loc),
            ⌜M !! id = some nd ∧ S !! id = some st'⌝ ∗ drvRes (GF := GF) γr id nd st')) ?_)
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
            (<[id0 := st]> S) !! id = some st'⌝ ∗ drvRes (GF := GF) γr id nd st'))).2
        iexists _, st
        isplitr
        · ipureintro; exact ⟨GMap.lookup_insert _ _ _, GMap.lookup_insert _ _ _⟩
        unfold drvRes
        iexists n
        rw [← Hiface]
        iframe HisNode Hdrv Hseq
        isplitr
        · ipureintro; rfl
        isplitr
        · iexists ms, γs
          iframe Hrec
        unfold runStor
        iexists ms, γs, vsl
        iframe Hrec Hstok Hci Hvoters Hvsl
        ipureintro
        exact ⟨Hcap, Int.le_refl _⟩
    ipureintro
    intro id Hid
    have Hne : id ≠ id0 := fun h => Hid0n (h ▸ Hid)
    rw [GMap.lookup_insert_ne _ _ (Ne.symm Hne), GMap.lookup_insert_ne _ _ (Ne.symm Hne)]
    exact Hdom id (by rw [Hdrop]; exact List.mem_cons_of_mem _ Hid)
  · have Hk3 : sint.nat k = 3 := by word
    rw [Hk3]
    simp only [show clusterIds.take 3 = clusterIds from rfl, show clusterIds.drop 3 = [] from rfl]
    clear Hdom Hk3
    imod ownMap_persist mP _ M $$ HmP with #HmP
    imod ownMap_persist mS _ S $$ HmS with #HmS
    ipersist peers
    ipersist storages
    -- the transport's transfer budget (2026-10-13): `timeouts` under its lock
    icases typedPointsto_split _ _ _ $$ «$r0» with Htrs
    try simp only [TypedPointsto.typedPointstoDef]
    icases Htrs with ⟨mu, left, -⟩
    imod sync.init_Mutex (transfersInv γr.cluster «$r0_ptr») ⊤ («$r0_ptr».[RTransfers, go!"mu"])
      $$ mu [left] with #Htr
    · inext
      unfold transfersInv
      iexists W64 1048576
      iframe left
    ihave #Htr' : isTransfers γr.cluster «$r0_ptr» $$ []
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
          ⌜M !! id = some nd ∧ S !! id = some st⌝ ∗ drvRes γr id nd st))
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
      have Hlt' : sint.nat k < clusterIds.length := by simp [clusterIds, kvVoters]; word
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
      icases Hres with ⟨%n, %Hgn, #HisNode, Hnode, #Hsrec, Hseq, Hrs⟩
      subst Hgn
      wp_apply wp_map_lookup1 go.uint64 _ mP M id0 DFrac.discard $$ HmP as -
      wp_apply wp_map_lookup1 go.uint64 _ mS S id0 DFrac.discard $$ HmS as -
      simp only [HMl, HSl, Option.getD_some]
      wp_apply (wp_New γr id0 n st _) $$ [Hnode Hseq Hrs]
      · iframe Hreg HisNode Hnode Hstatic Hxfer Hsrec Hseq Hrs
        unfold sendSpec
        imodintro
        iintro %src %msl %ms %Φ'
        imodintro
        iintro ⟨Hmsl, Hmsok⟩ HΦ'
        wp_auto
        wp_apply (wp_deliver γr.cluster mP «$r0_ptr» M src msl ms)
          $$ [$Hmsl $Hmsok]
        · iframe #
        iapply HΦ'
        itrivial
      iintro %r ⟨%γp, #Hisreg⟩
      wp_apply wp_slice_literal (V := Loc) [r]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hks $Hkcap $Hsl2] as %ksl' ⟨Hks, Hkcap, -⟩
      wp_apply wp_map_lookup1 go.uint64 _ mP M id0 DFrac.discard $$ HmP as -
      simp only [HMl, Option.getD_some]
      wp_apply wp_fork $$ []
      · wp_apply (wp_tick γr.cluster id0 n) $$ []
        · iframe HisNode
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
