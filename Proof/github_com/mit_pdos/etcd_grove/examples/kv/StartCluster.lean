/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/StartCluster.lean`. Lean-first (no
Rocq counterpart).

The cluster bring-up of the store's `Main`, at any storage registry (`[KVStor GF]`), over raft's
unified API (2026-10-30, stage P of the client repair): raft's cluster of the voters `1, 2, 3`
with no boot log, its conf entries decided by the store's rule, the store's invariant and its
registry of the snapshots made (`kvCluster_alloc`: `cluster_alloc`, `confPolicy_alloc` at
`kvConfN`, `rkvInv_alloc`, `kvSnapInv_alloc`), then a first loop over the voters: each storage
(`NewStorage`: its records and `NewMemoryStorage`'s tokens) gives `RestartNode`'s `restartStorage`
at the empty contents (`kvStorage_bootStorage`), whose frame, the storage's invariant at `kvJ γ K` for
the key `K` raft names, comes back in `RestartNode`'s post; with `memSnapNone_open`'s `memSnapLb γs 0`
it makes `runStor`. `RestartNode` (2026-11-01, durability layer 4: from allocation's `raftState` at
`RaftState.init` and `nodeVacant`, its update firing at once and leaving `raftState`; `HardState{}`,
the conf state `kvConfState clusterIds`: the voters, no `AutoLeave`) gives the node, its driver token
at the storage's key, its configuration view and its running token `nodeRunning … 1`, into `peers`
and `storages` (`drvRes`). (Blocked on API gap G1, `stageI-5-clients.md`: the frame cannot carry the
invariant at the key the driver records.) Then the transfer budget and the `send`
closure (`deliver`), and a second loop that starts each replica (`New`), appends it to `kvs` and
forks its `tick`.
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
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Reconf

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
node (`isNode`), its driver token idle on the store's storage at its key `K` (2026-11-01, durability
layer 4), its durable state (`raftState`, at `RaftState.init`), its configuration view and
(2026-10-30) its running token, the storage's record, the replica's sequence-number token, and what
`run` holds of the storage (`runStor`, persistent, at the same key; until 2026-10-30 the storage's
snapshot token). -/
def drvRes (γr : RKVNames) (id : w64) (nd : GoInterface) (st : Loc) : IProp GF :=
  iprop(∃ (n : Loc) (K : GName), ⌜nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
    isNode n γr.cluster kvRaftN id ∗
    nodeDriver n γr.cluster kvRaftN (NodeDriverState.init (kvStorIface st) K) ∗
    raftState γr.cluster id RaftState.init ∗
    EtcdGrove.nodeConfig n γr.cluster kvRaftN ⟨0, kvMembership⟩ ∗
    (∃ (ms : Loc) (γs : MemStorNames), kvStorRec st ms γs) ∗
    nodeRunning n γr.cluster kvRaftN 1 ∗
    id ↪[γr.seq] W64 0 ∗ runStor γr K st)

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
    (wp_RestartNode : RestartNode.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG)) :
    StartCluster.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end reg

end proof

end kv
end EtcdGrove
end Perennial
