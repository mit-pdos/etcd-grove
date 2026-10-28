/-
# Raft's node API: dynamic clusters, the implementation (2026-10-27)

The definitions behind the draft's dynamic-cluster items (`InvNode.lean`, "What etcd's server
needs") and the proofs of their laws and specs (`*_impl`), from raft's dynamic mode
(`RNMode.dyn`, `raft_dyn_alloc_boot`'s allocation, `node.ApplyConfChange`'s dynamic case,
`node.Advance`'s A1) and its no-snapshot mode.

- **A membership** (`Membership`) is a `tracker.Config` (`cfgOf`); its `confchange` state is the
  canonical one (`stOf`: every voter tracked as a voter, every learner as a learner), which is
  every reachable state's (`cfgStateC_of_good`). A change applies `ccStepB` to it.
- **A dynamic cluster** (`isDynamicCluster`): the cluster's nodes are in the mode
  `.dyn (decOf decode) (stOf c0)` (`Cluster.mode`), in raft's no-snapshot mode.
- **A node's configuration view** (`nodeConfig`): raft's `nodeCfg` of the node's names, apart from
  its `Ready` loop's token; the cluster's table (`nodeTabOk`) makes the names of the node's
  predicates agree.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApi
public import Proof.go_etcd_io.raft.v3.CCApplyC
public import Proof.go_etcd_io.raft.v3.SnapConf
public import Proof.go_etcd_io.raft.v3.Protocol.ResultsDyn
public import Proof.go_etcd_io.raft.v3.Protocol.SnapMint
import all Proof.go_etcd_io.raft.v3.InvNodeChan

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## Memberships -/

section pure
variable [GooseExts]

/-- A membership as a `tracker.Config`. -/
def cfgOf (m : Membership) : CfgM :=
  ⟨m.voters, m.votersOutgoing, m.learners, m.learnersNext, m.autoLeave⟩

/-- A `tracker.Config` as a membership. -/
def memOf (c : CfgM) : Membership :=
  ⟨c.incoming, c.outgoing, c.learners, c.learnersNext, c.autoLeave⟩

theorem cfgOf_memOf (c : CfgM) : cfgOf (memOf c) = c := by cases c; rfl

theorem memOf_cfgOf (m : Membership) : memOf (cfgOf m) = m := by cases m; rfl

/-- A membership's `confchange` state: the canonical one (`cfgStateC`). -/
def stOf (m : Membership) : CCState := cfgStateC (cfgOf m)

theorem stOf_cfg (m : Membership) : (stOf m).cfg = cfgOf m := rfl

theorem stOf_simple (vs : GSet w64) : stOf (Membership.simple vs) = cfgState vs ∅ :=
  cfgStateC_simple vs ∅

/-- A reachable state is its membership's. -/
theorem stOf_memOf {s : CCState} (h : CCGood s) : stOf (memOf s.cfg) = s := by
  unfold stOf; rw [cfgOf_memOf]; exact cfgStateC_of_good h

/-- The draft's `Membership.Valid`: a configuration a node can be in, reachable. -/
def memValid (m : Membership) : Prop := CfgOk (stOf m) ∧ CCGood (stOf m)

/-- The draft's `Membership.applyChange`: `ccStepB` of the change as `AsV2` makes it. -/
def memApply (o : ConfChangeIM) (m : Membership) : Option Membership :=
  (ccStepB (ccV2Of o) (stOf m)).map fun s => memOf s.cfg

/-- `ccStepB`'s answer is `ccApplyM`'s, of fewer than `2^62` tracked ids. -/
theorem ccStepB_some' {op : CCOp} {s s' : CCState} (h : ccStepB op s = some s') :
    ccApplyM op.1 op.2 s = some s' ∧ GMap.size s'.cfg.ids < 2 ^ 62 := by
  unfold ccStepB at h
  cases h1 : ccApplyM op.1 op.2 s with
  | none => rw [h1] at h; cases h
  | some s2 =>
    rw [h1] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h; exact ⟨rfl, by assumption⟩
    · cases h

/-- A change's result, as a state. -/
theorem memApply_some {o : ConfChangeIM} {m m' : Membership} (hg : CCGood (stOf m))
    (h : memApply o m = some m') :
    ccStepB (ccV2Of o) (stOf m) = some (stOf m') ∧ CCGood (stOf m') := by
  unfold memApply at h
  cases hs : ccStepB (ccV2Of o) (stOf m) with
  | none => rw [hs] at h; cases h
  | some s' =>
    rw [hs] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hg' : CCGood s' := ccApplyM_good hg _ _ (ccStepB_some' hs).1
    rw [stOf_memOf hg']
    exact ⟨rfl, hg'⟩

theorem memValid_simple (vs : GSet w64) (hne : vs ≠ ∅) (Hsz : GMap.size vs < 2 ^ 62) :
    memValid (Membership.simple vs) := by
  unfold memValid; rw [stOf_simple]
  exact ⟨cfgOk_cfgState vs hne Hsz, ccGood_cfgState vs⟩

theorem memApply_valid (o : ConfChangeIM) (m m' : Membership) :
    memValid m → memApply o m = some m' → memValid m' := by
  intro ⟨hok, hg⟩ h
  obtain ⟨hs, hg'⟩ := memApply_some hg h
  obtain ⟨ha, hb⟩ := ccStepB_some' hs
  exact ⟨(ccApplyM_overlap ha hok hb).2, hg'⟩

/-- `memApply` at a simple membership, from `ccStepB`. -/
theorem memApply_simple (o : ConfChangeIM) (vs vs' : GSet w64)
    (h : ccStepB (ccV2Of o) (cfgState vs ∅) = some (cfgState vs' ∅)) :
    memApply o (Membership.simple vs) = some (Membership.simple vs') := by
  unfold memApply; rw [stOf_simple, h]; rfl

theorem memValid_simple_facts {vs : GSet w64} (h : memValid (Membership.simple vs)) :
    vs ≠ ∅ ∧ GMap.size vs < 2 ^ 62 := by
  unfold memValid at h; rw [stOf_simple] at h
  have h2 := h.1.2.2
  rw [cfgState_empty_ids] at h2
  exact ⟨h.1.2.1, h2⟩

theorem memApply_nodeZero (vs : GSet w64) (cm : ConfChangeM) :
    cm.nodeId = W64 0 → memValid (Membership.simple vs) →
    memApply (.v1 cm) (Membership.simple vs) = some (Membership.simple vs) := by
  intro H0 Hv
  obtain ⟨hne, Hsz⟩ := memValid_simple_facts Hv
  apply memApply_simple
  unfold ccStepB
  rw [ccApplyM_v1_noop vs cm H0 hne ∅ (fun k hk => absurd hk (GMap.not_elem_of_empty _))]
  simp only [Option.bind_some]
  rw [cfgState_empty_ids, ite_eq_left Hsz]

theorem memApply_addVoter (vs : GSet w64) (cm : ConfChangeM) :
    cm.type = W32 0 → cm.nodeId ∈ vs → memValid (Membership.simple vs) →
    memApply (.v1 cm) (Membership.simple vs) = some (Membership.simple vs) := by
  intro Hty Hin Hv
  by_cases H0 : cm.nodeId = W64 0
  · exact memApply_nodeZero vs cm H0 Hv
  obtain ⟨-, Hsz⟩ := memValid_simple_facts Hv
  apply memApply_simple
  unfold ccStepB ccV2Of
  simp only
  rw [ccApplyM_single_simple]
  have Hc : ({ Type' := cm.type, NodeId' := cm.nodeId } : ConfChangeSingleM) = addNodeCC cm.nodeId := by
    rw [Hty]
  rw [Hc, simpleM_cfgState_addNode vs ∅ cm.nodeId H0 (GMap.not_elem_of_empty _)
    (fun k hk => absurd hk (GMap.not_elem_of_empty _))]
  rw [GMap.insert_id _ _ _ ((GMap.elem_of_gset _ _).1 Hin)]
  simp only [Option.bind_some]
  rw [cfgState_empty_ids, ite_eq_left Hsz]

theorem memApply_removeVoter (vs : GSet w64) (cm : ConfChangeM) :
    cm.type = W32 1 → cm.nodeId ≠ W64 0 → cm.nodeId ∈ vs →
    (GMap.delete cm.nodeId vs : GSet w64) ≠ ∅ → memValid (Membership.simple vs) →
    memApply (.v1 cm) (Membership.simple vs) =
      some (Membership.simple (GMap.delete cm.nodeId vs)) := by
  intro Hty H0 Hin Hne Hv
  obtain ⟨-, Hsz⟩ := memValid_simple_facts Hv
  exact memApply_simple _ _ _ (ccStepB_removeVoter vs cm Hty H0 Hin Hne Hsz)

theorem memApply_removeAbsent (vs : GSet w64) (cm : ConfChangeM) :
    cm.type = W32 1 → cm.nodeId ≠ W64 0 → cm.nodeId ∉ vs → memValid (Membership.simple vs) →
    memApply (.v1 cm) (Membership.simple vs) = some (Membership.simple vs) := by
  intro Hty H0 Hin Hv
  obtain ⟨hne, Hsz⟩ := memValid_simple_facts Hv
  exact memApply_simple _ _ _ (ccStepB_removeAbsent vs cm Hty H0 Hin hne Hsz)

/-- A `ConfState` reporting a state's configuration reports its membership. -/
theorem confStateIs_of_ok (cs : ConfStateM) (c : CfgM) (h : confstateOk cs c) :
    confStateIs cs (memOf c) := h

/-- The decoder as raft takes it (`CCDec`): the client's, on the entries as the client sees them,
its change as `AsV2` makes it, applied (2026-10-28, stage U6m: the client's decoder rejects
nothing). -/
def decOf (decode : ConfChangeDecoder) : CCDec :=
  fun D e => (decode (strip D) (LogEntry.ofEntryM e)).map fun o => .apply (ccV2Of o)

end pure


/-! ## A dynamic cluster -/

section dyn
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What a dynamic cluster's names say: its nodes in the dynamic mode of the decoder `decode` and
the initial membership `c0`, in raft's no-snapshot mode, with no snapshot directory. -/
def DynNames (γ : Cluster) (c0 : Membership) (decode : ConfChangeDecoder) : Prop :=
  ∃ (h0 : CfgOk (stOf c0)) (h1 : CCGood (stOf c0)),
    γ.mode = (RNMode.dyn (decOf decode) (stOf c0) h0 h1).all ∧
    γ.raft.reNoSnap = true ∧ γ.raft.reSnapLoc = (fun _ => none)

/-- **The cluster is dynamic** (the draft's `isDynamicCluster`). -/
def isDynamicCluster (γ : Cluster) (N : Namespace) (c0 : Membership)
    (decode : ConfChangeDecoder) : IProp GF :=
  iprop(⌜DynNames γ c0 decode⌝ ∗ clusterInv γ N)

instance isDynamicCluster_persistent (γ : Cluster) (N : Namespace) (c0 : Membership)
    (decode : ConfChangeDecoder) : Persistent (isDynamicCluster (GF := GF) γ N c0 decode) := by
  unfold isDynamicCluster; infer_instance

theorem DynNames.noSnap {γ : Cluster} {c0 : Membership} {decode : ConfChangeDecoder}
    (h : DynNames γ c0 decode) : γ.raft.reNoSnap = true := by
  obtain ⟨-, -, -, h, -⟩ := h; exact h

/-- A node of a dynamic cluster is in its dynamic mode. -/
theorem DynNames.node {γ : Cluster} {c0 : Membership} {decode : ConfChangeDecoder}
    {γn : NodeNames} (h : DynNames γ c0 decode) (hn : NodeOk γ γn) :
    ∃ h0 h1, γn.mode = .dyn (decOf decode) (stOf c0) h0 h1 := by
  obtain ⟨h0, h1, hm, -⟩ := h
  refine ⟨h0, h1, ?_⟩
  rw [hn.2.2.2.1, hm, RNMode.all_self]

theorem DynNames.isDyn {γ : Cluster} {c0 : Membership} {decode : ConfChangeDecoder}
    {γn : NodeNames} (h : DynNames γ c0 decode) (hn : NodeOk γ γn) : γn.mode.isDyn = true := by
  obtain ⟨h0, h1, hm⟩ := h.node hn
  rw [hm]; rfl

theorem sentMsg_dynamic_notSnapshot_impl (γ : Cluster) (N : Namespace) (c0 : Membership)
    (decode : ConfChangeDecoder) (src : w64) (st : MsgSt) :
    isDynamicCluster (GF := GF) γ N c0 decode ∗ sentMsg γ N src st ⊢ ⌜st.msg.Type' ≠ MsgSnap⌝ := by
  unfold isDynamicCluster sentMsg isRaftMsg
  iintro ⟨⟨%Hd, -⟩, -, ⟨%Hns, -⟩, -⟩
  ipureintro; exact Hns Hd.noSnap

theorem readySnap_dynamic_impl (γ : Cluster) (N : Namespace) (c0 : Membership)
    (decode : ConfChangeDecoder) (rd : Ready) (st : NodeDriverState) (ce : List LogEntry)
    (es : List EntryM) (l : SnapLoan) :
    isDynamicCluster (GF := GF) γ N c0 decode ∗ readySnap γ N rd st ce es (some l) ⊢ False := by
  unfold isDynamicCluster
  simp only [readySnap]
  unfold snapshotCert
  iintro ⟨⟨%Hd, -⟩, -, -, -, ⟨%Hns, -⟩, -⟩
  rw [Hd.noSnap] at Hns; cases Hns

/-- **A node's boot token** of a new dynamic cluster (the draft's `nodeDynamicBoot`): the cluster
dynamic, of the peers, raft's ghost state at the bootstrap state in the cluster's mode
(`bootInit`), the committed bootstrap log, the bytes of its entries, the term budget, and the
node's table, empty. -/
def nodeDynamicBoot (γ : Cluster) (N : Namespace) (ps : List w64) (ctxs : List (List w8))
    (id : w64) : IProp GF :=
  iprop((∃ c0 decode, isDynamicCluster γ N c0 decode) ∗
    ⌜BootLogOk ps γ.raft.reBoot ∧ γ.raft.reCfg = GMap.listToSet ps⌝ ∗
    bootInit γ.raft (γ.mode inferInstance) id (GMap.listToSet ps) γ.raft.reBoot ∗
    isCommitted γ.raft γ.raft.reBoot ∗ bootMarshal ps ctxs γ.raft.reBoot ∗
    inv budgetN (budgetInv γ.bud) ∗ termLB γ.bud (W64 1) ∗
    (∃ g : GName, ⌜γ.nodeTab !! id = some g⌝ ∗ ghostMapAuth g 1 (∅ : GMap w64 CfgNames)))

/-- A node's dynamic ghost state at the bootstrap state, from the allocation's. -/
theorem ownRaftGhostR_boot (γr : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64)
    (bootLog : List EntryM) (hL : (bootLog.length : Int) < 2 ^ 64) :
    ownRaftGhost (GF := GF) γr id (initPStateAt (W64 1) bootLog) true ⊢
      ownRaftGhostR γr dec c0 id (rboot c0 bootLog) := by
  iintro Hg
  unfold ownRaftGhostR
  rw [show (rboot c0 bootLog).p = initPStateAt (W64 1) bootLog from rfl]
  iframe Hg
  isplitr; · ipureintro; exact RInv_rboot dec c0 bootLog hL
  isplitr
  · unfold logRecs rboot
    iapply (BigSepL.bigSepL_nil).2; iempintro
  iintro %h
  exfalso; exact absurd h (by simp [initPStateAt, initPState])

/-- **A new dynamic cluster** (the draft's `dynamicCluster_alloc`). -/
theorem dynamicCluster_alloc_impl (N : Namespace) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) (decode : ConfChangeDecoder) (transfer : Bool) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 →
    BootLog ps ctxs boot → ps.Nodup → ps ≠ [] → W64 0 ∉ ps → (ps.length : Int) ≤ 2 ^ 62 →
    ⊢ bootMarshal (GF := GF) ps ctxs (LogEntry.toEntries boot 0) -∗
      |={E}=> ∃ γ, ⌜γ.raft.reBoot.length = boot.length⌝ ∗ ownCommittedOps γ boot ∗ ownReadCtxs γ ∅ ∗ readCredits γ (2 ^ 64 - 2) ∗
        isDynamicCluster γ N (Membership.simple (GMap.listToSet ps)) decode ∗
        (if transfer then leaderTransferOn γ N else leaderTransferOff γ N) ∗
        [∗list] id ∈ ps, nodeDynamicBoot γ N ps ctxs id := by
  intro Hrb HB Hnd Hne Hnz _
  iintro #Hm
  imod budget_alloc_boot (GF := GF) Hrb E with ⟨%bud, #Hbinv, #Htlb⟩
  imod alloc_maps (GF := GF) (K := w64) (V := CfgNames) (GMap.listToSet ps) with ⟨%tab, -, Htab⟩
  have Hok := (BootLog_ok HB)
  have Hwf := Hok.wf Hnd
  have Hbne : LogEntry.toEntries boot 0 ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [toEntries_length, HB.1] at this
    exact Hne (List.eq_nil_of_length_eq_zero this)
  have HbL : ((LogEntry.toEntries boot 0).length : Int) < 2 ^ 64 := by
    rw [toEntries_length]; have := HB.2.1; omega
  have Hcne := listToSet_ne_empty ps Hne
  have Hnz' : W64 0 ∉ GMap.listToSet ps := fun h => Hnz ((GMap.elem_of_list_to_set _ _).1 h)
  have Hsz : GMap.size (GMap.listToSet ps) < 2 ^ 62 := by
    rw [GMap.size_list_to_set ps Hnd]; have := HB.2.1; rw [HB.1] at this; omega
  have Hv := memValid_simple (GMap.listToSet ps) Hcne Hsz
  let c0 := Membership.simple (GMap.listToSet ps)
  let md : RNMode := .dyn (decOf decode) (stOf c0) Hv.1 Hv.2
  let dc := DynCfg.ofFold (decOf decode) (stOf c0) Hv.1
  ihave Hcl := api_alloc_client (GF := GF) N E (GMap.listToSet ps) ps ctxs boot bud md tab
    (some (DynCfg.all dc)) HB
  imod ownRaftGhost_alloc_core E (GMap.listToSet ps) (GMap.listToSet ps) (some (DynCfg.all dc))
    (fun _ _ => True) (LogEntry.toEntries boot 0) (W64 1) (allocOut N boot bud md tab) none
    (fun _ h => by cases h) true (fun _ => Hbne) (!transfer) (fun _ => Hbne)
    (sokOf (fun _ _ => False)) (fun _ => none) (N .@ "raft") N Hcne Hnz' Hwf
    (fun _ => by rw [show uint.Z (W64 1) = 1 from rfl]; exact Int.le_refl _)
    $$ Hcl with ⟨%γr, %Hγ, #Hcinv, #Hc0, Hnodes, Hout, Hcr, -⟩
  obtain ⟨Hcfg, Hdyn, -, Hboot, -, Hns, Hnx, -, Hsl, HNs, -⟩ := Hγ
  iunfold allocOut at Hout
  icases Hout with ⟨%γ, %Hγr, #HspT, #Hinv, Hops, Hctx⟩
  obtain ⟨Hγr, Hγb, Hγm, Hγt⟩ := Hγr
  subst Hγr
  ihave #Hdc : isDynamicCluster (GF := GF) γ N c0 decode $$ []
  · unfold isDynamicCluster clusterInv
    iframe Hcinv Hinv HspT
    ipureintro
    exact ⟨⟨Hv.1, Hv.2, Hγm, Hns, Hsl⟩, HNs⟩
  imodintro
  iexists γ
  isplitr
  · ipureintro; rw [Hboot, toEntries_length]
  iframe Hops Hctx Hdc
  isplitl [Hcr]
  · unfold readCredits; iexact Hcr
  isplitr
  · iapply leaderTransfer_of γ N transfer Hnx
  simp only [Option.isSome_some]
  ihave Hn := bigSepM_listToSet _ ps Hnd $$ Hnodes
  ihave Ht := bigSepM_listToSet (fun x => iprop(∃ γx, ⌜tab !! x = some γx⌝ ∗
    ghostMapAuth (GF := GF) γx 1 (∅ : GMap w64 CfgNames))) ps Hnd $$ Htab
  ihave H := (BigSepL.bigSepL_sep_eqv).2 $$ [Hn Ht]
  · iframe Hn Ht
  iapply BigSepL.bigSepL_impl $$ H
  imodintro
  iintro %k %id %_ ⟨Hg, ⟨%g, %Hg0, Ha⟩⟩
  unfold nodeDynamicBoot
  rw [Hboot, Hγb, Hγt, Hγm, RNMode.all_self]
  iframe Hc0 Hm Hbinv Htlb
  isplitr
  · iexists c0, decode; iexact Hdc
  isplitr
  · ipureintro; exact ⟨Hok, Hcfg⟩
  isplitl [Hg]
  · unfold bootInit
    isplitr
    · ipureintro
      refine ⟨?_, stOf_simple _⟩
      unfold RaftNames.dyn; rw [Hdyn]; simp [DynCfg.all_self, dc]
    iapply ownRaftGhostR_boot γ.raft _ _ id _ HbL $$ Hg
  iexists g
  iframe Ha
  ipureintro; exact Hg0

end dyn

/-! ## A node's configuration view and delivered log -/

section view
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A dynamic node's configuration view** (the draft's `nodeConfig`): raft's view of the
configuration (`nodeCfg`) of the node's names, at the membership's state, the names the node's
(`nodeTabOk`). -/
def nodeConfig (n : Loc) (γ : Cluster) (_N : Namespace) (v : ConfigView) : IProp GF :=
  iprop(∃ (γn : NodeNames) (id : w64),
    ⌜NodeOk γ γn ∧ γn.mode.isDyn = true ∧ CCGood (stOf v.membership)⌝ ∗
    EtcdGrove.isNodeChan γn id n ∗ nodeTabOk γ id γn ∗ nodeCfg γn v.applied (stOf v.membership))

/-- **The committed log delivered to node `n` extends `l`** (the draft's `deliveredLogLb`):
raft's lower bound (`dlvLb`) of the node's names (its table's, if dynamic), and committed. -/
def deliveredLogLb (n : Loc) (γ : Cluster) (_N : Namespace) (l : List LogEntry) : IProp GF :=
  iprop((∃ (γn : NodeNames) (id : w64) (ds : List EntryM), ⌜NodeOk γ γn ∧ strip ds = l⌝ ∗
    EtcdGrove.isNodeChan γn id n ∗ (⌜γn.mode.isDyn = false⌝ ∨ nodeTabOk γ id γn) ∗ dlvLb γn ds) ∗
    isCommittedLogLb γ l)

instance deliveredLogLb_persistent (n : Loc) (γ : Cluster) (N : Namespace) (l : List LogEntry) :
    Persistent (deliveredLogLb (GF := GF) n γ N l) := by
  unfold deliveredLogLb; infer_instance

theorem drv_isNode_lb (γn : NodeNames) (id : w64) (n : Loc) (ds : List EntryM) (p : HardStateM) :
    EtcdGrove.nodeDriverChan (GF := GF) γn id n ds p ⊢
      EtcdGrove.nodeDriverChan γn id n ds p ∗ (EtcdGrove.isNodeChan γn id n ∗ dlvLb γn ds) := by
  unfold EtcdGrove.nodeDriverChan
  iintro ⟨#Hn, Hd, #Hlb, Hr⟩
  iframe Hn Hd Hlb Hr

theorem busy_isNode_lb (γn : NodeNames) (id : w64) (n : Loc) (ds es : List EntryM)
    (p : HardStateM) (L : Option SnapLoan) :
    nodeDriverBusy (GF := GF) γn id n ds es p L ⊢
      nodeDriverBusy γn id n ds es p L ∗ (EtcdGrove.isNodeChan γn id n ∗ dlvLb γn ds) := by
  unfold nodeDriverBusy
  iintro ⟨#Hn, #Hlb, Hr⟩
  iframe Hn Hlb Hr

theorem nodeDriver_deliveredLogLb_impl (n : Loc) (γ : Cluster) (N : Namespace)
    (st : NodeDriverState) :
    nodeDriver (GF := GF) n γ N st ⊢ nodeDriver n γ N st ∗ deliveredLogLb n γ N st.delivered := by
  unfold nodeDriver
  iintro ⟨%γn, %id, %ds, %Hf, #Hci, #Hlb0, Hst, #Hdy, Htok⟩
  ihave #Hl : iprop(EtcdGrove.isNodeChan (GF := GF) γn id n ∗ dlvLb γn ds) $$ [Htok]
  · icases Htok with (⟨-, Htok⟩ | ⟨%es, %L, -, Htok⟩)
    · icases drv_isNode_lb γn id n ds st.hardState $$ Htok with ⟨-, $⟩
    · icases busy_isNode_lb γn id n ds es st.hardState L $$ Htok with ⟨-, $⟩
  ihave #Htb : iprop(⌜γn.mode.isDyn = false⌝ ∨ nodeTabOk (GF := GF) γ id γn) $$ []
  · icases Hdy with (%H | ⟨#H, -, -⟩)
    · ileft; ipureintro; exact H
    · iright; iexact H
  icases Hl with ⟨#Hnd, #Hdl⟩
  isplitl [Hst Htok]
  · iexists γn, id, ds
    iframe Hci Hlb0 Hst Hdy Htok
    ipureintro; exact Hf
  unfold deliveredLogLb
  iframe Hlb0
  iexists γn, id, ds
  iframe Hnd Htb Hdl
  ipureintro; exact ⟨Hf.1, Hf.2.2⟩

theorem deliveredLogLb_mono_impl (n : Loc) (γ : Cluster) (N : Namespace) (l1 l2 : List LogEntry) :
    l1 <+: l2 → deliveredLogLb (GF := GF) n γ N l2 ⊢ deliveredLogLb n γ N l1 := by
  intro Hp
  unfold deliveredLogLb
  iintro ⟨⟨%γn, %id, %ds, %Hf, #Hnd, #Htb, #Hdl⟩, #Hlb⟩
  isplitl []
  · iexists γn, id, ds.take l1.length
    iframe Hnd Htb
    isplitr
    · ipureintro
      refine ⟨Hf.1, ?_⟩
      unfold strip; rw [List.map_take]
      show (strip ds).take l1.length = l1
      rw [Hf.2]; exact (List.prefix_iff_eq_take.1 Hp).symm
    unfold dlvLb
    iapply monoListLbOwn_le _ (List.take_prefix _ _) $$ Hdl
  iapply isCommittedLogLb_mono_impl γ l1 l2 Hp $$ Hlb

theorem deliveredLogLb_committed_impl (n : Loc) (γ : Cluster) (N : Namespace) (l : List LogEntry) :
    deliveredLogLb (GF := GF) n γ N l ⊢ isCommittedLogLb γ l := by
  unfold deliveredLogLb
  iintro ⟨-, #H⟩; iexact H

theorem committedAtTerm_committed_impl (γ : Cluster) (N : Namespace) (t c : w64) :
    committedAtTerm (GF := GF) γ N t c ⊢
      ∃ l, isCommittedLogLb γ l ∗ ⌜l.length = uint.nat c⌝ := by
  unfold committedAtTerm
  iintro ⟨-, H⟩; iexact H

theorem nodeDriver_hardStateCommitted_impl (n : Loc) (γ : Cluster) (N : Namespace)
    (c0 : Membership) (decode : ConfChangeDecoder) (st : NodeDriverState) :
    isDynamicCluster (GF := GF) γ N c0 decode ∗ nodeDriver n γ N st ⊢ nodeDriver n γ N st ∗
      (⌜st.hardState = hsZero⌝ ∨
        committedAtTerm γ N st.hardState.Term' st.hardState.Commit' ∗
          ⌜(st.delivered.length : Int) ≤ uint.Z st.hardState.Commit'⌝) := by
  unfold isDynamicCluster nodeDriver
  iintro ⟨⟨%Hdn, -⟩, %γn, %id, %ds, %Hf, #Hci, #Hlb0, Hst, #Hdy, Htok⟩
  have Hd := Hdn.isDyn Hf.1
  icases Hdy with (%H | ⟨#Htb, #Hhc, #Hcl⟩)
  · rw [Hd] at H; cases H
  isplitl [Hst Htok]
  · iexists γn, id, ds
    iframe Hci Hlb0 Hst Htok
    isplitr
    · ipureintro; exact Hf
    iright; iframe Htb Hhc Hcl
  iunfold hsCommitted at Hhc
  icases Hhc with (%H | H | %H)
  · ileft; ipureintro; exact H
  · iright; iexact H
  · exfalso; rw [Hdn.noSnap] at H; cases H

/-- A `MsgSnap` carries no credit. -/
theorem msgCredits_snapshot_impl (γ : Cluster) (N : Namespace) (st : MsgSt) :
    st.msg.Type' = MsgSnap → ⊢ |==> msgCredits (GF := GF) γ N st := by
  intro Hty
  unfold msgCredits stTks
  have h1 : st.msg.Type' ≠ MsgReadIndex := by rw [Hty]; simp [MsgSnap, MsgReadIndex]
  have h2 : st.msg.Type' ≠ MsgProp := by rw [Hty]; simp [MsgSnap, MsgProp]
  rw [ite_eq_right h1, ite_eq_right h2]
  imod rdCred_zero_upd γ.raft with H
  imodintro
  iframe H

/-- The `.snap` clause of `isMessage` does not read the `ConfState` lists or `AutoLeave` (as the
server's `isMessage_snap_lists`). -/
theorem isMessage_snap_lists' (γr : RaftNames) (m : Msg) (cl : CSLists) (al : Bool)
    (h : m.ty = .snap) :
    isMessage (GF := GF) γr { m with cl := cl, al := al } = isMessage γr m := by
  rcases m with ⟨ty, src, dst, term, reject, index, logterm, commit, rejecthint, entries, cl0, al0,
    ctx⟩
  simp only at h
  subst h
  rfl

/-- **A raft `MsgSnap` with the client's snapshot in place of raft's** (the draft's
`sentMsg_replaceSnapshot`): raft's `isMessage_snap_recontent`, at the committed log `l` up to the
new snapshot, whose last term is the snapshot's. -/
theorem sentMsg_replaceSnapshot_impl (γ : Cluster) (N : Namespace) (src : w64) (st : MsgSt)
    (sv sv' : SnapshotM) (c : w64) (l : List LogEntry) (E : CoPset) :
    ↑N ⊆ E → st.msg.Type' = MsgSnap → st.snap = some sv →
    uint.Z sv.Metadata'.Index' ≤ uint.Z sv'.Metadata'.Index' →
    uint.Z sv'.Metadata'.Index' ≤ uint.Z c →
    l.length = uint.nat sv'.Metadata'.Index' →
    l.getLast?.map LogEntry.term = some sv'.Metadata'.Term' →
    ⊢ sentMsg (GF := GF) γ N src st -∗ committedAtTerm γ N st.msg.Term' c -∗
      isCommittedLogLb γ l -∗ snapshotCert γ N (snapTrip sv' sv'.Metadata'.ConfState'.lists) ={E}=∗
      sentMsg γ N src { st with snap := some sv' } := by
  intro HE Hty Hsn Hix Hc Hl Hlt
  iintro #Hs #Hca #Hlb #Hk
  unfold sentMsg
  icases Hs with ⟨#Hci, #Hrm, #Htlb, -⟩
  ihave #Hci' := Hci
  iunfold clusterInv at Hci'
  icases Hci' with ⟨%HNs, #Hcinv, -, -⟩
  imod raft_of_snapshotCert γ N E HE _ $$ Hci Hk with #HkD
  iunfold raftSnapCertD at HkD
  icases HkD with ⟨#Hrc, #Hdat⟩
  imod api_lb_committed γ N E HE l $$ Hci Hlb with ⟨%A, %HA, #HAc⟩
  iunfold committedAtTerm at Hca
  icases Hca with ⟨#Hw, -⟩
  iunfold isRaftMsg at Hrm
  icases Hrm with ⟨%Hns, %Hsent, ⟨%a, %Habs, #Hmsgs⟩, -, %Hra⟩
  have Ha : a = some (absSnap st.msg sv sv.Metadata'.ConfState'.lists) := by
    rcases Habs with ⟨Hn, -⟩ | ⟨ty', Hty', Hne, -⟩ | ⟨sv0, -, Hsv, rfl⟩
    · rw [Hty, mtypeOf_MsgSnap] at Hn; cases Hn
    · rw [Hty, mtypeOf_MsgSnap] at Hty'; cases Hty'; exact absurd rfl Hne
    · rw [Hsn] at Hsv; cases Hsv; rfl
  subst Ha
  simp only [Option.toList_some]
  icases BigSepL.bigSepL_cons.1 $$ Hmsgs with ⟨#HmC, -⟩
  ihave #Hm := isMessageC_isMessage γ.raft _ $$ HmC
  have HAlen : (A.length : Int) = uint.Z sv'.Metadata'.Index' := by
    have h1 : A.length = l.length := by rw [← HA, strip_length]
    have h2 := rUnat_eq sv'.Metadata'.Index'
    omega
  have HAlast : A.getLast?.map EntryM.Term' = some sv'.Metadata'.Term' := by
    rw [← Hlt, ← HA]; unfold strip; rw [List.getLast?_map, Option.map_map]; rfl
  have HlogN : (↑(raftLogN γ.raft) : CoPset) ⊆ E := by
    intro p hp
    unfold raftLogN raftN at hp; rw [HNs] at hp
    exact HE p (nclose_subseteq N "raft" p (nclose_subseteq (N .@ "raft") "log" p hp))
  have Hterm : (absSnap st.msg sv sv.Metadata'.ConfState'.lists).term = st.msg.Term' := rfl
  ihave #Hw' : commitWit γ.raft (absSnap st.msg sv sv.Metadata'.ConfState'.lists).term c $$ []
  · rw [Hterm]; iexact Hw
  imod isMessage_snap_recontent γ.raft E (absSnap st.msg sv sv.Metadata'.ConfState'.lists) c
    sv'.Metadata'.Index' sv'.Metadata'.Term' A HlogN rfl Hix Hc HAlen HAlast $$ Hcinv Hm Hw' HAc
    with #Hm'
  have Hvo := isMessage_snap_lists' (GF := GF) γ.raft
    { absSnap st.msg sv sv.Metadata'.ConfState'.lists with
      index := sv'.Metadata'.Index', logterm := sv'.Metadata'.Term' }
    sv'.Metadata'.ConfState'.lists sv'.Metadata'.ConfState'.AutoLeave' rfl
  imodintro
  iframe Hci Htlb
  isplitl
  rotate_left
  · unfold sentSnapCert
    iright
    iexists sv'
    iframe Hk
    ipureintro; rfl
  iunfold isRaftMsg
  isplitr
  · ipureintro; exact Hns
  isplitr
  · ipureintro
    exact fun h => (Hsent h).of_msg rfl Hra.1 (by rw [Hty]; simp [MsgSnap, MsgApp])
  isplitr
  · iexists some (absSnap st.msg sv' sv'.Metadata'.ConfState'.lists)
    isplitr
    · ipureintro
      right; right
      exact ⟨sv', by simp only; rw [Hty]; exact mtypeOf_MsgSnap, rfl, rfl⟩
    simp only [Option.toList_some]
    iapply BigSepL.bigSepL_cons.2
    isplitl
    · have Heq : absSnap st.msg sv' sv'.Metadata'.ConfState'.lists =
          { { absSnap st.msg sv sv.Metadata'.ConfState'.lists with
              index := sv'.Metadata'.Index', logterm := sv'.Metadata'.Term' } with
            cl := sv'.Metadata'.ConfState'.lists, al := sv'.Metadata'.ConfState'.AutoLeave' } := rfl
      iapply isMessageC_intro
      · rw [Heq, Hvo]; iexact Hm'
      unfold msgCert; iright
      have Hk : raftSnapCert (GF := GF) γ.raft
          (msgSnapTrip (absSnap st.msg sv' sv'.Metadata'.ConfState'.lists)) =
          raftSnapCert γ.raft (snapTrip sv' sv'.Metadata'.ConfState'.lists) := by
        unfold raftSnapCert; rfl
      rw [Hk]; iexact Hrc
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · unfold msgDat
    iintro !> %sv0 %Hsv
    obtain ⟨-, Hsv⟩ := Hsv
    simp only [Option.some.injEq] at Hsv
    subst Hsv
    have Hd : snapDataOk (GF := GF) γ.raft
        (snapTrip sv' sv'.Metadata'.ConfState'.lists).sid.index'
        (snapTrip sv' sv'.Metadata'.ConfState'.lists).dat =
        snapDataOk γ.raft sv'.Metadata'.Index' sv'.Data' := rfl
    rw [← Hd]; iexact Hdat
  ipureintro; exact Hra

/-- No conf entry in a range of the delivered log is none in raft's. -/
theorem noConfIn_of_strip (ds : List EntryM) (lo hi : Nat) (H : NoConfChangeIn (strip ds) lo hi) :
    NoConfIn ds lo hi := by
  intro k e h1 h2 he hc
  apply H k (LogEntry.ofEntryM e) h1 h2
  · unfold strip; rw [List.getElem?_map, he]; rfl
  · exact hc

end view

/-! ## The dynamic specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

end spec

end ApiImpl
end EtcdGrove
end Perennial
