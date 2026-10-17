/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Main.lean`. Lean-first (no
Rocq counterpart).

Every callee's spec is taken at any storage registry (`∀ [RegStor GF]`): the proof allocates
the registry and instantiates them at it.

**Raft v3.7 (2026-10-16, stage R6b).** `RestartNode` takes the register's storage under the
register's `StorageModel` (`regStorage_isStorage`) and its `InitialState` closure
(`regStorage_initialState`); the conf state it returns is `regConfState clusterIds` (the voters,
no `AutoLeave`: `al = false`, which `RestartNode.spec` admits since stage R6b).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.NewStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Storage__InitialState
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Storage__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__Put
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__Read
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__TransferLeadership
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Register__RemoveMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.deliver
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.tick
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.quietLogger__Debugf
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.quietLogger__Errorf
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.quietLogger__Infof
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.quietLogger__Warningf
public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.RegStorageInstance
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Alloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

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
theorem regCC_cluster (γn : NodeNames) (Hok : γn.raft.reCCOk = ccOkR)
    (Hmd : γn.mode = .dyn (ccDecOf opR) c0R c0R_ok c0R_good) : RegCC γn opR c0R c1R :=
  ⟨⟨c0R_ok, c0R_good, Hmd⟩, fun ty bs h => by rw [Hok] at h; exact h, opR_step0, opR_step1, rfl⟩

/-- `RemoveMember(3)`'s change is one the cluster admits. -/
theorem rm3_allowed (γ : RaftNames) (Hok : γ.reCCOk = ccOkR) : CCAllowed γ (.v1 (rmCC (W64 3))) := by
  intro bs Hbs
  rw [Hok]
  exact ⟨rfl, rmCC (W64 3), Hbs, rfl⟩

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

/-- The configuration `Main` starts node `id` with, on the storage `st`. -/
abbrev nodeConfig (id : w64) (st : Loc) : Config :=
  { ID' := id, ElectionTick' := W64 10, HeartbeatTick' := W64 1,
    Storage' := interface.mkOk (go.GoType.PointerType rStorageTy) #st,
    Applied' := 0, AsyncStorageWrites' := false, MaxSizePerMsg' := W64 1048576,
    MaxCommittedSizePerReady' := 0, MaxUncommittedEntriesSize' := 0,
    MaxInflightMsgs' := W64 256, MaxInflightBytes' := 0, CheckQuorum' := false,
    PreVote' := false, ReadOnlyOption' := 0,
    Logger' := interface.mkOk qLoggerTy #qLoggerV,
    DisableProposalForwarding' := false, DisableConfChangeValidation' := false,
    StepDownOnRemoval' := true, TraceLogger' := GoInterface.nil,
    DisableProposalForwardingCallback' := func.nil }

theorem nodeConfig_valid (id : w64) (st : Loc) (h : id ∈ clusterIds) :
    ConfigValid (nodeConfig id st) := by
  simp only [clusterIds, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold ConfigValid
  rcases h with rfl | rfl | rfl <;> simp <;> decide

section reg
variable [RegStor GF]

/-- What `Main` holds of a replica between starting its node and starting its register: the
node's driver token (with the node, `isNode`, in it), the storage's record and the replica's
sequence-number token. -/
def drvRes (γr : RegNames) (bud : BudgetNames) (id : w64) (nd : GoInterface) (st : Loc) :
    IProp GF :=
  iprop(∃ (γn : NodeNames) (n : Loc),
    ⌜γn.raft = γr.raft ∧ γn.bud = bud ∧ γn.stor = regStorIface st ∧
      nd = interface.mkOk (go.GoType.PointerType node.ty) #n⌝ ∗
    nodeDriver γn id n [] ∗ (∃ (ms : Loc) (γs : MemStorNames), regStorRec st ms γs) ∗
    id ↪[γr.seq] W64 0 ∗
    -- (2026-10-15, stage N) the node's mode and the driver's view of its configuration
    ⌜RegCC γn opR c0R c1R⌝ ∗ nodeCfg γn 0 c0R)

theorem opCred_split (γp : RepNames) (a b : Nat) :
    opCred (GF := GF) γp (a + b) ⊣⊢ opCred γp a ∗ opCred γp b := by
  unfold opCred
  rw [show (◯ (a + b) : Auth Nat) = (◯ a) • (◯ b) from Auth.frag_op]
  exact own_op _ _ _

end reg

theorem Main.wp_proof
    (wp_NewStorage : ∀ [RegStor GF], register.NewStorage.spec (GF := GF) (hG := hG))
    (wp_InitialState : ∀ [RegStor GF], register.Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : ∀ [RegStor GF], register.Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_New : ∀ [RegStor GF], register.New.spec (GF := GF) (hG := hG))
    (wp_Put : ∀ [RegStor GF], register.Register.Put.spec (GF := GF) (hG := hG))
    (wp_Get : ∀ [RegStor GF], register.Register.Get.spec (GF := GF) (hG := hG))
    (wp_Read : ∀ [RegStor GF], register.Register.Read.spec (GF := GF) (hG := hG))
    (wp_TransferLeadership : ∀ [RegStor GF],
      register.Register.TransferLeadership.spec (GF := GF) (hG := hG))
    (wp_RemoveMember : ∀ [RegStor GF], register.Register.RemoveMember.spec (GF := GF) (hG := hG))
    (wp_deliver : ∀ [RegStor GF], register.deliver.spec (GF := GF) (hG := hG))
    (wp_tick : ∀ [RegStor GF], register.tick.spec (GF := GF) (hG := hG))
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG))
    (wp_RestartNode : ∀ [RegStor GF], RestartNode.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  wp_start
  -- the storage registry
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorRec) with ⟨%γreg, Hreg⟩
  letI : RegStor GF := ⟨γreg⟩
  imod regStorInv_alloc (GF := GF) ⊤ $$ Hreg with #HstorInv
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %vsl ⟨Hvsl, -⟩
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := GoInterface) as %mP HmP
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mS HmS
  have Hsz : go.arrayLiteralSize [KeyedElement none (ElementExpression go.uint64 #(W64 1)),
      KeyedElement none (ElementExpression go.uint64 #(W64 2)),
      KeyedElement none (ElementExpression go.uint64 #(W64 3))] = 3 := rfl
  have Hl : (([W64 1, zero_val w64, zero_val w64].set (sint.nat (W64 (0 + 1))) (W64 2)).set
      (sint.nat (W64 (0 + 1 + 1))) (W64 3)) = clusterIds := rfl
  rw [Hsz, Hl]
  imod ownSlice_persist _ _ _ $$ Hvsl with #Hvsl
  -- raft's ghost state for the cluster and the term budget (2026-10-14, stage R) with the
  -- register's invariant, the client's half of the value and the sequence-number tokens,
  -- allocated from the client's share once raft's names exist: the register builds the standing
  -- update for raft's own entries (`reg_noopAu`)
  imod raft_dyn_alloc (GF := GF) ⊤ (ccDecOf opR) c0R c0R_ok (GMap.listToSet clusterIds) ccOkR
    (fun γ => iprop(∃ γr : RegNames, ⌜γr.raft = γ⌝ ∗ regInv γr ∗ regVal γr [] ∗
      ([∗map] id ↦ s ∈ constMap clusterIds (W64 0), id ↪[γr.seq] s)))
    (by rw [GMap.elem_of_list_to_set]; decide) $$ []
    with ⟨%γ, %Hcfg', #Hcinv, ⟨%γr, %Hγr, #Hreg, Hval, Hseqs⟩, Hghosts, #Hc0,
      HrdC, #HrdI⟩
  · unfold allocClient
    iintro %γ0 %_ #_ HcL Hfresh HrdF
    imod regInv_alloc (GF := GF) ⊤ γ0 (constMap clusterIds (W64 0)) $$ HcL Hfresh HrdF
      with ⟨%γr0, %Hγr0, #Hreg0, Hval0, Hseqs0⟩
    ihave #Hnoop := reg_noopAu γr0 $$ Hreg0
    subst Hγr0
    imodintro
    iframe Hnoop
    iexists γr0
    iframe Hreg0 Hval0 Hseqs0
    ipureintro; rfl
  have Hcfg : γ.reCfg = GMap.listToSet clusterIds := Hcfg'.2.2
  have Hdyn := Hcfg'.1
  have HccOk := Hcfg'.2.1
  imod budget_alloc (GF := GF) (3 * ticksN + timeoutsN) (by unfold ticksN timeoutsN; omega) ⊤
    with ⟨%bud, #Hbinv, Hcred, #Hlb0⟩
  icases (tickCred_split bud (3 * ticksN) timeoutsN).1 $$ Hcred with ⟨Hcred, Htcred⟩
  -- the clients' invariant
  imod ghostVar_alloc (GF := GF) false with ⟨%γf, Hf⟩
  icases ghostVar_halves γf false $$ Hf with ⟨Hf1, Hf2⟩
  imod inv_alloc clientN ⊤ (clientInvBody (GF := GF) γr γf) $$ [Hval Hf1] with #Hcl
  · inext
    unfold clientInvBody
    iexists [], false
    iframe Hval Hf1
    ipureintro; intro h; cases h
  ihave #Hcl : clientInv (GF := GF) γr γf $$ [Hcl]
  · unfold clientInv; iexact Hcl
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
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z (W64 3) := ⟨Hk.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z k) _ DFrac.discard id0 Hk.1 $$ [Hvsl] as -
    · iframe Hvsl; ipureintro; exact Hid0
    wp_apply (wp_NewStorage _ clusterIds) $$ [$HstorInv $Hvsl] as %st ⟨%ms, %γs, #Hrec, #Hvoters, Hmem⟩
    have Hid0m : id0 ∈ clusterIds := List.mem_of_getElem? Hid0
    rw [drop_cons_of_getElem? _ _ _ Hid0]
    icases Htodo with ⟨⟨Hghost, Hseq⟩, Htodo⟩
    ihave #Hlogger := qLogger_isLogger wp_Debugf wp_Errorf wp_Infof wp_Warningf
    ihave #Hstor := regStorage_isStorage wp_Snapshot st ms γs $$ Hpkg Hrec
    ihave #Hinit := regStorage_initialState wp_InitialState st _ clusterIds memStorEmpty
      $$ Hpkg Hvoters Hvsl
    have Hiface : regStorIface st = GoInterface.ok ⟨go.GoType.PointerType rStorageTy, #st⟩ := rfl
    rw [Hiface]
    ihave Hown : regOwnStorage (interface.ok ⟨go.GoType.PointerType rStorageTy, #st⟩) memStorEmpty
      $$ [Hmem]
    · unfold regOwnStorage
      iexists st, ms, γs
      iframe Hrec Hmem
      ipureintro; rfl
    ihave Hown : ownStorage (interface.ok ⟨go.GoType.PointerType rStorageTy, #st⟩) memStorEmpty
      $$ Hown
    ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
    · iPkgInit
    ihave Hghost : rnInit γr.raft (.dyn (ccDecOf opR) c0R c0R_ok c0R_good) id0
        (GMap.listToSet clusterIds) $$ [Hghost]
    · iunfold rnInit
      isplitr
      · ipureintro; exact ⟨Hdyn, rfl⟩
      iexact Hghost
    -- (PR raft#88) no proposal-forwarding callback
    ihave #Hpcb : pfcbImpl (GF := GF) func.nil none $$ []
    · iunfold pfcbImpl; ipureintro; rfl
    wp_apply (wp_RestartNode γr.raft (.dyn (ccDecOf opR) c0R c0R_ok c0R_good)
      bud _ (nodeConfig id0 st) qLogger
      ⟨go.GoType.PointerType rStorageTy, #st⟩ memStorEmpty (HardStateM.mk (W64 0) (W64 0) (W64 0))
      (register.regConfState clusterIds) none
      (nodeConfig_valid id0 st Hid0m) rfl rfl
      (by show sint.Z (W64 256) < 2 ^ 62; decide) rfl rfl rfl rfl
      (by right; show W64 1048576 ≠ W64 0; decide)
      rfl rfl rfl rfl rfl (by left; rfl) rfl ⟨rfl, rfl, rfl⟩
      (by decide) clusterIds_nodup (by decide) (by decide) rfl rfl rfl rfl Hcfg Hid0m
      (fun _ => rfl))
      $$ [$Hraftinit $«$a0» $Hlogger $Hstor $Hown $Hpcb $Hinit $Hghost $Hc0 $Hbinv $Hlb0]
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
        ipureintro; exact regCC_cluster γn (by rw [Hr]; exact HccOk) Hmd
    ipureintro
    intro id Hid
    have Hne : id ≠ id0 := fun h => Hid0n (h ▸ Hid)
    rw [GMap.lookup_insert_ne _ _ (Ne.symm Hne), GMap.lookup_insert_ne _ _ (Ne.symm Hne)]
    exact Hdom id (by rw [Hdrop]; exact List.mem_cons_of_mem _ Hid)
  · have Hk3 : sint.nat k = 3 := by word
    rw [Hk3]
    simp only [show clusterIds.take 3 = clusterIds from rfl, show clusterIds.drop 3 = [] from rfl]
    imod ownMap_persist mP _ M $$ HmP with #HmP
    ipersist peers
    -- the transport's transfer budget (2026-10-13): `timeouts` tick credits under its lock
    icases typedPointsto_split _ _ _ $$ «$r0» with Htrs
    try simp only [TypedPointsto.typedPointstoDef]
    icases Htrs with ⟨mu, left, -⟩
    imod sync.init_Mutex (transfersInv bud «$r0_ptr») ⊤ («$r0_ptr».[RTransfers, go!"mu"])
      $$ mu [left Htcred] with #Htr
    · inext
      unfold transfersInv
      iexists W64 1048576
      iframe left
      rw [show uint.nat (W64 1048576) = timeoutsN from rfl]
      iexact Htcred
    ihave #Htr' : isTransfers bud «$r0_ptr» $$ []
    · unfold isTransfers; iexact Htr
    ipersist tr
    wp_apply wp_map_make1 (K := w64) (V := Loc) as %mR HmR
    ihave IH2 : iprop(∃ (k : w64) (idv : w64) (R : GMap w64 Loc),
        "i" ∷ i_ptr ↦ k ∗ "id" ∷ id_ptr ↦ idv ∗ "HmR" ∷ mR ↦$ R ∗ "HmS" ∷ mS ↦$ S ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 3⌝ ∗
        "Hcred" ∷ tickCred bud ((3 - sint.nat k) * ticksN) ∗
        "Hregs" ∷ ([∗list] id ∈ clusterIds.take (sint.nat k), ∃ (r : Loc) (γp : RepNames),
          ⌜R !! id = some r⌝ ∗ isRegister γr γp r ∗ opCred γp (2 ^ 64 - 1)) ∗
        "Hdrv" ∷ ([∗list] id ∈ clusterIds.drop (sint.nat k), ∃ (nd : GoInterface) (st : Loc),
          ⌜M !! id = some nd ∧ S !! id = some st⌝ ∗ drvRes γr bud id nd st) ∗
        "%Hdom" ∷ ⌜∀ id, id ∈ clusterIds.drop (sint.nat k) → R !! id = none⌝)
      $$ [i id HmR HmS Hcred Hdone]
    · iexists W64 0, _, ∅
      iframe i id HmR HmS
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero, Nat.sub_zero]
      iframe Hcred Hdone
      isplitr
      · ipureintro; constructor <;> word
      isplitr
      · iapply (BigSepL.bigSepL_nil).2; iempintro
      ipureintro; intro id _; rfl
    wp_for IH2
    wp_if_destruct
    · have Hlt : sint.Z k < 3 := by word
      have Hlt' : sint.nat k < clusterIds.length := by simp [clusterIds]; word
      obtain ⟨id0, Hid0⟩ : ∃ id0, clusterIds[sint.nat k]? = some id0 :=
        ⟨_, List.getElem?_eq_getElem Hlt'⟩
      have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z (W64 3) := ⟨Hk.1, by word⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z k) _ DFrac.discard id0 Hk.1 $$ [Hvsl] as -
      · iframe Hvsl; ipureintro; exact Hid0
      have Hdrop := drop_cons_of_getElem? _ _ _ Hid0
      have Hnd' : (clusterIds.drop (sint.nat k)).Nodup :=
        clusterIds_nodup.sublist (List.drop_sublist _ _)
      rw [Hdrop] at Hnd'
      have Hid0n : id0 ∉ clusterIds.drop (sint.nat k + 1) := (List.nodup_cons.mp Hnd').1
      have HR0 := Hdom id0 (by rw [Hdrop]; exact List.mem_cons_self)
      rw [Hdrop]
      icases Hdrv with ⟨⟨%nd, %st, %Hlk, Hres⟩, Hdrv⟩
      obtain ⟨HMl, HSl⟩ := Hlk
      unfold drvRes
      icases Hres with ⟨%γn, %n, %Hgn, Hnode, #Hsrec, Hseq, %Hmd, Hncfg⟩
      obtain ⟨Hr, Hb, Hs, rfl⟩ := Hgn
      wp_apply wp_map_lookup1 go.uint64 _ mP M id0 DFrac.discard $$ HmP as -
      wp_apply wp_map_lookup1 go.uint64 _ mS S id0 (DFrac.own 1) $$ [$HmS] as HmS
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
        iintro ⟨Hmsl, Hmsok, Hcr⟩ HΦ'
        rw [Hr, Hb]
        wp_auto
        wp_apply (wp_deliver γr.raft bud mP «$r0_ptr» M msl ms)
          $$ [$Hmsl $Hmsok $Hcr]
        · iframe #
        iapply HΦ'
        itrivial
      iintro %r ⟨%γp, %Hγp, #Hisreg, Hopc⟩
      wp_auto
      wp_apply wp_mapInsert go.uint64 mR R id0 r $$ [$HmR] as HmR
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
      have Hcr : (3 - sint.nat k) * ticksN = ticksN + (3 - (sint.nat k + 1)) * ticksN := by
        have : sint.nat k < 3 := by word
        rw [show 3 - sint.nat k = (3 - (sint.nat k + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul,
          Nat.add_comm]
      rw [Hcr]
      icases (tickCred_split bud ticksN _).1 $$ Hcred with ⟨Hc1, Hcred⟩
      ihave Hregs' : iprop([∗list] id ∈ clusterIds.take (sint.nat k + 1), ∃ (r' : Loc)
          (γp' : RepNames), ⌜(<[id0 := r]> R) !! id = some r'⌝ ∗ isRegister (GF := GF) γr γp' r' ∗
            opCred γp' (2 ^ 64 - 1)) $$ [Hregs Hopc]
      · rw [take_succ_of_getElem? _ _ _ Hid0]
        iapply (BigSepL.bigSepL_append (Φ := fun _ id => iprop(∃ (r' : Loc) (γp' : RepNames),
            ⌜(<[id0 := r]> R) !! id = some r'⌝ ∗ isRegister (GF := GF) γr γp' r' ∗
              opCred γp' (2 ^ 64 - 1)))).2
        isplitl [Hregs]
        · iapply (BigSepL.bigSepL_mono (Φ := fun _ id => iprop(∃ (r' : Loc) (γp' : RepNames),
              ⌜R !! id = some r'⌝ ∗ isRegister (GF := GF) γr γp' r' ∗
                opCred γp' (2 ^ 64 - 1))) ?_) $$ Hregs
          intro j x Hx
          have Hxt : x ∈ clusterIds.take (sint.nat k) := List.mem_of_getElem? Hx
          have Hne : x ≠ id0 := take_drop_ne clusterIds clusterIds_nodup (sint.nat k) x id0 Hxt
            (by rw [Hdrop]; exact List.mem_cons_self)
          iintro ⟨%r', %γp', %Hl, Hres⟩
          iexists r', γp'
          iframe Hres
          ipureintro
          rw [GMap.lookup_insert_ne _ _ (Ne.symm Hne)]
          exact Hl
        · iapply (BigSepL.bigSepL_singleton (Φ := fun _ id => iprop(∃ (r' : Loc) (γp' : RepNames),
            ⌜(<[id0 := r]> R) !! id = some r'⌝ ∗ isRegister (GF := GF) γr γp' r' ∗
              opCred γp' (2 ^ 64 - 1)))).2
          iexists r, γp
          iframe Hisreg Hopc
          ipureintro; exact GMap.lookup_insert _ _ _
      wp_apply wp_fork $$ [Hc1]
      · wp_apply (wp_tick γn' id0 n') $$ [Hc1]
        · iframe HisNode'
          rw [Hb']
          iexact Hc1
        itrivial
      wp_for_post
      iframe
      iexists k + W64 1, id0, <[id0 := r]> R
      have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      rw [Hk1]
      iframe
      isplitr
      · ipureintro; constructor <;> word
      ipureintro
      intro id Hid
      have Hne : id ≠ id0 := fun h => Hid0n (h ▸ Hid)
      rw [GMap.lookup_insert_ne _ _ (Ne.symm Hne)]
      exact Hdom id (by rw [Hdrop]; exact List.mem_cons_of_mem _ Hid)
    · have Hk3' : sint.nat k = 3 := by word
      rw [Hk3']
      simp only [show clusterIds.take 3 = [W64 1, W64 2, W64 3] from rfl]
      ihave ⟨⟨%r1, %γp1, %HR1, #Hreg1, Hop1⟩, Hregs⟩ := (BigSepL.bigSepL_cons).1 $$ Hregs
      ihave ⟨⟨%r2, %γp2, %HR2, #Hreg2, Hop2⟩, Hregs⟩ := (BigSepL.bigSepL_cons).1 $$ Hregs
      ihave ⟨⟨%r3, %γp3, %HR3, #Hreg3, Hop3⟩, -⟩ := (BigSepL.bigSepL_cons).1 $$ Hregs
      rw [show (2 : Nat) ^ 64 - 1 = 1 + (2 ^ 64 - 2) by decide]
      icases (opCred_split γp1 1 _).1 $$ Hop1 with ⟨Hop1, -⟩
      icases (opCred_split γp2 1 _).1 $$ Hop2 with ⟨Hop2, -⟩
      icases (opCred_split γp3 1 _).1 $$ Hop3 with ⟨Hop3, -⟩
      rw [show (2 : Nat) ^ 64 - 2 = 1 + (2 ^ 64 - 3) by decide]
      icases (rdCred_split γr.raft 1 _).1 $$ HrdC with ⟨HrdC, -⟩
      imod ownMap_persist mR _ R $$ HmR with #HmR
      ipersist regs
      wp_apply chan.wp_make2 (V := Bool) (W64 1) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
      · ipureintro; decide
      ihave Hoc : ownChan γc Bool (.Buffered []) $$ Hoc
      imod start_handoff ch (fun (_ : Bool) => ghostVar (GF := GF) γf (1 : Qp).half true)
        iprop(True) iprop(False) γc $$ Hch Hoc with ⟨%γh, %Hγh, #Hho, Hprod, Hcons⟩
      ipersist done
      wp_apply wp_fork $$ [Hop1 Hf2 Hprod]
      · -- client A: `Put("hello")`, then the flag to B
        wp_auto
        wp_apply wp_map_lookup1 go.uint64 _ mR R (W64 1) DFrac.discard $$ HmR as -
        simp only [HR1, Option.getD_some]
        ihave Hau := client_put_au γr γf $$ Hcl Hf2
        wp_apply (wp_Put γr γp1 r1 helloB _ (by unfold helloB; decide)) $$ [Hop1 Hau] as Hf
        · iframe Hop1 Hau Hreg1
        wp_apply wp_handoff_send (t := go.bool) γh ch
          (fun (_ : Bool) => ghostVar (GF := GF) γf (1 : Qp).half true) iprop(True) iprop(False)
          true $$ [$Hho $Hprod $Hf] as -
        · itrivial
      wp_apply +noauto wp_handoff_receive (t := go.bool) γh ch
        (fun (_ : Bool) => ghostVar (GF := GF) γf (1 : Qp).half true) iprop(True) iprop(False)
        false $$ [$Hho $Hcons] as %v %ok ⟨-, Hgot⟩
      unfold handoffGot
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases ok
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hgot with ⟨-, Hf⟩
        iexfalso; iexact Hf
      simp only [↓reduceIte]
      icases Hgot with ⟨Hf, -⟩
      wp_auto
      wp_apply wp_map_lookup1 go.uint64 _ mR R (W64 2) DFrac.discard $$ HmR as -
      simp only [HR2, Option.getD_some]
      ihave Hau := client_get_au γr γf $$ Hcl Hf
      wp_apply (wp_Get γr γp2 r2 (fun x => iprop(⌜x = helloB⌝))) $$ [Hop2 Hau] as %x %Hx
      · iframe Hop2 Hau Hreg2
      subst Hx
      wp_auto
      -- B's read by read index on replica 3, from the empty history's lower bound
      wp_apply wp_map_lookup1 go.uint64 _ mR R (W64 3) DFrac.discard $$ HmR as -
      simp only [HR3, Option.getD_some]
      wp_apply (wp_Read γr γp3 r3 []) $$ [Hop3 HrdC]
        as %y -
      · iframe Hop3 HrdC Hreg3
        unfold regLb
        iexists [], []
        iframe Hc0
        isplitl
        · iapply BigSepL2.bigSepL2_nil.2; itrivial
        ipureintro; rfl
      -- (2026-10-15, stage N) B asks replica 1 to remove replica 3 from the cluster
      try wp_auto
      wp_apply wp_map_lookup1 go.uint64 _ mR R (W64 1) DFrac.discard $$ HmR as -
      simp only [HR1, Option.getD_some]
      wp_apply (wp_RemoveMember γr γp1 r1 (W64 3) (rm3_allowed γr.raft HccOk)) $$ [$Hreg1]
      -- B asks every replica to hand the leadership over to replica 2 (2026-10-13; to 3 until
      -- 2026-10-15)
      try wp_auto
      wp_apply wp_map_lookup1 go.uint64 _ mR R (W64 1) DFrac.discard $$ HmR as -
      simp only [HR1, Option.getD_some]
      wp_apply (wp_TransferLeadership γr γp1 r1 (W64 2)) $$ [$Hreg1]
      try wp_auto
      wp_apply wp_map_lookup1 go.uint64 _ mR R (W64 2) DFrac.discard $$ HmR as -
      simp only [HR2, Option.getD_some]
      wp_apply (wp_TransferLeadership γr γp2 r2 (W64 2)) $$ [$Hreg2]
      try wp_auto
      wp_apply wp_map_lookup1 go.uint64 _ mR R (W64 3) DFrac.discard $$ HmR as -
      simp only [HR3, Option.getD_some]
      wp_apply (wp_TransferLeadership γr γp3 r3 (W64 2)) $$ [$Hreg3]
      try wp_auto
      iapply HΦ
      itrivial

end proof

end register
end EtcdGrove
end Perennial
