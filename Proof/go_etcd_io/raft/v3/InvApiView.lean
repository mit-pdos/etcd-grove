/-
# Raft's node API: memberships and a node's view (2026-10-27; 2026-10-29, U9: from `InvApiDyn.lean`)

The definitions behind the node API's memberships and a node's configuration view and delivered
log, with the proofs of their laws (`*_impl`). (Until U9, 2026-10-29, `InvApiDyn.lean`, which also
held the dynamic cluster `isDynamicCluster` and its specs, deleted with the static and dynamic API
families; this file keeps its other two sections.)

- **A membership** (`Membership`) is a `tracker.Config` (`cfgOf`); its `confchange` state is the
  canonical one (`stOf`: every voter tracked as a voter, every learner as a learner), which is
  every reachable state's (`cfgStateC_of_good`). A change applies `ccStepB` to it.
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

theorem stOf_simple (vs : GSet w64) : stOf (Membership.simple vs) = cfgState vs ∅ :=
  cfgStateC_simple vs ∅

/-- A reachable state is its membership's. -/
theorem stOf_memOf {s : CCState} (h : CCGood s) : stOf (memOf s.cfg) = s := by
  unfold stOf; rw [cfgOf_memOf]; exact cfgStateC_of_good h

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

end pure

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
  unfold nodeDriver deliveredLogLb
  iintro ⟨%γn, %id, %ds, %Hf, #Hci, #Hlb0, %Hdyn, #Htab, #Hhc, Htok⟩
  icases Htok with (⟨%Hn, Htok⟩ | ⟨%es, %L, %Hh, Htok, Hm⟩)
  · icases drv_isNode_lb γn id n ds st.hardState $$ Htok with ⟨Htok, #Hnd, #Hdl⟩
    isplitl [Htok]
    · iexists γn, id, ds
      isplitr; · ipureintro; exact Hf
      isplitr; · iexact Hci
      isplitr; · iexact Hlb0
      isplitr; · ipureintro; exact Hdyn
      isplitr; · iexact Htab
      isplitr; · iexact Hhc
      ileft
      iframe Htok
      ipureintro; exact Hn
    isplitr
    · iexists γn, id, ds
      isplitr; · ipureintro; exact ⟨Hf.1, Hf.2.2⟩
      isplitr; · iexact Hnd
      isplitr; · iright; iexact Htab
      iexact Hdl
    iexact Hlb0
  · icases busy_isNode_lb γn id n ds es st.hardState L $$ Htok with ⟨Htok, #Hnd, #Hdl⟩
    isplitl [Htok Hm]
    · iexists γn, id, ds
      isplitr; · ipureintro; exact Hf
      isplitr; · iexact Hci
      isplitr; · iexact Hlb0
      isplitr; · ipureintro; exact Hdyn
      isplitr; · iexact Htab
      isplitr; · iexact Hhc
      iright
      iexists es, L
      iframe Htok Hm
      ipureintro; exact Hh
    isplitr
    · iexists γn, id, ds
      isplitr; · ipureintro; exact ⟨Hf.1, Hf.2.2⟩
      isplitr; · iexact Hnd
      isplitr; · iright; iexact Htab
      iexact Hdl
    iexact Hlb0

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
    icases Hdl with ⟨#Hm, #Hk⟩
    isplitl []
    · iapply monoListLbOwn_le _ (List.take_prefix _ _) $$ Hm
    ihave #Hk' := (dlvKeysAt_app γn.sn 0 (ds.take l1.length) (ds.drop l1.length)).1 $$ [Hk]
    · rw [List.take_append_drop]; iexact Hk
    icases Hk' with ⟨#H1, -⟩
    iexact H1
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

/-- (2026-10-29, S1) In a `dup` cluster a proposal's tickets are persistent. -/
theorem entTks_persist_impl (γ : RaftNames) (h : γ.dup = true) :
    ∀ es : List EntryM, ([∗list] e ∈ es, entTk (GF := GF) γ e) ⊢ □ [∗list] e ∈ es, entTk γ e
  | [] => by
    iintro -
    imodintro
    iapply (BigSepL.bigSepL_nil (Φ := fun _ e => entTk (GF := GF) γ e)).2
    iempintro
  | e :: es => by
    iintro H
    icases (BigSepL.bigSepL_cons (Φ := fun _ e => entTk (GF := GF) γ e)).1 $$ H with ⟨He, Hs⟩
    ihave #Hs := entTks_persist_impl γ h es $$ Hs
    ihave He : □ entTk (GF := GF) γ e $$ [He]
    · unfold entTk
      split
      · iclear He; imodintro; iempintro
      · iapply propTk_persist γ _ h $$ He
    icases He with #He
    imodintro
    iapply (BigSepL.bigSepL_cons (Φ := fun _ e => entTk (GF := GF) γ e)).2
    iframe He Hs

/-- (2026-10-29, S1) In a `dup` cluster a `MsgProp`'s credits are persistent: no read credit, its
tickets persistent. -/
theorem msgCredits_copy_impl (γ : Cluster) (N : Namespace) (st : MsgSt) :
    γ.raft.dup = true → st.msg.Type' = MsgProp →
    msgCredits (GF := GF) γ N st ⊢ □ msgCredits γ N st := by
  intro Hd Hty
  unfold msgCredits stTks
  rw [if_pos Hty]
  iintro Hts
  iapply entTks_persist_impl γ.raft Hd st.ents $$ Hts

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
  icases Hs with ⟨#Hci, #Hrm, #Htlb, -, #Hpool, %HU⟩
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
  icases Hrm with ⟨%Hsh, ⟨%a, %Habs, #Hmsgs⟩, -, %Haf, #Hxw⟩
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
  have Hsh' : SentMsgShape { st with snap := some sv' } := by
    obtain ⟨h1, h2, h3, h4, h5, -, h7, h8⟩ := Hsh
    exact ⟨h1, h2, h3, h4, h5, fun h => absurd h (by rw [Hty]; simp [MsgSnap, MsgApp]), h7, h8⟩
  imodintro
  isplitr; · iexact Hci
  isplitr
  · iunfold isRaftMsg
    isplitr; · ipureintro; exact Hsh'
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
    isplitr; · ipureintro; exact Haf
    iexact Hxw
  isplitr; · iexact Htlb
  isplitr
  · unfold sentSnapCert
    iright
    iexists sv'
    iframe Hk
    ipureintro; rfl
  isplitr; · iexact Hpool
  ipureintro; exact HU

/-- No conf entry in a range of the delivered log is none in raft's. -/
theorem noConfIn_of_strip (ds : List EntryM) (lo hi : Nat) (H : NoConfChangeIn (strip ds) lo hi) :
    NoConfIn ds lo hi := by
  intro k e h1 h2 he hc
  apply H k (LogEntry.ofEntryM e) h1 h2
  · unfold strip; rw [List.getElem?_map, he]; rfl
  · exact hc

end view

end ApiImpl
end EtcdGrove
end Perennial
