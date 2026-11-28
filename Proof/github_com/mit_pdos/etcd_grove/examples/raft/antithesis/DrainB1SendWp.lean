/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E: `DrainB1Phases.lean`'s
`drainSendB1.stmt` proved: `node.drain`'s send loop (`node.drain.sendE`, S4's `DrainSendWp` over the
parity vocabulary), over the `Ready`'s messages, each frozen first (`frozenMsg`, raft's `msgOwnZ`
read-only). For each: `early` is `false` (no `isRequest` skip); the cause reported (`reportCause`,
`causeOwn_report`: the handled message's `recv`, or nothing); the `send` report built (`sendEv`) and
emitted (`emit`, `report_upd`): a protocol message's `evSend` (`sendHstep`, raft's facts grown by
the message's, `sendExt_b1`) or a transfer message's `evSendX` (`sendXHstep`); the message handed
to `sendMsg` with its `sendFacts` (a proposal not forwarded, or in flight: `netFacts_of_pend`,
`xnetFacts_of_ready`). The pending messages' facts are the run's invariant's at the first view
(`drainMid_peek`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Phases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Ext
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RangeRo
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Report
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__reportCause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sendEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__emit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__sendMsg
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

theorem mtypeOf_propose_s {t : w32} (H : mtypeOf t = some .propose) : t = MsgProp := by
  have key : ∀ k : Int, uint.Z t = k → t = W32 k := fun k hk => by rw [← hk]; simp
  unfold mtypeOf at H
  split at H <;> cases H
  rename_i hk; rw [key _ hk]; rfl

/-- A transfer reading's type and term. -/
theorem xmsgOf_type {st : MsgSt} {x : XMsg} (h : xmsgOf st = some x) :
    (st.msg.Type' = MsgTimeoutNow ∨ st.msg.Type' = MsgTransferLeader) ∧ x.term = st.msg.Term' := by
  unfold xmsgOf at h
  by_cases h1 : st.msg.Type' = MsgTimeoutNow
  · rw [if_pos h1] at h; cases h; exact ⟨.inl h1, rfl⟩
  · rw [if_neg h1] at h
    by_cases h2 : st.msg.Type' = MsgTransferLeader
    · rw [if_pos h2] at h; cases h; exact ⟨.inr h2, rfl⟩
    · rw [if_neg h2] at h; cases h

theorem xmsgOf_ne_snap {st : MsgSt} {x : XMsg} (h : xmsgOf st = some x) : st.msg.Type' ≠ MsgSnap := by
  intro hs
  have e := congrArg mtypeOf hs
  rw [show mtypeOf MsgSnap = some .snap from rfl] at e
  rcases (xmsgOf_type h).1 with h1 | h1 <;> rw [h1] at e
  · rw [show mtypeOf MsgTimeoutNow = none from rfl] at e; cases e
  · rw [show mtypeOf MsgTransferLeader = none from rfl] at e; cases e

/-- The pending lists after the `i`th message: a protocol message's reading heads the first. -/
theorem filterMap_drop_some {β : Type _} {f : QMsg → Option β} {ms : List QMsg} {i : Nat}
    (hi : i < ms.length) {b : β} (h : f ms[i] = some b) :
    (ms.drop i).filterMap f = b :: (ms.drop (i + 1)).filterMap f := by
  rw [List.drop_eq_getElem_cons hi, List.filterMap_cons, h]

theorem filterMap_drop_none {β : Type _} {f : QMsg → Option β} {ms : List QMsg} {i : Nat}
    (hi : i < ms.length) (h : f ms[i] = none) :
    (ms.drop i).filterMap f = (ms.drop (i + 1)).filterMap f := by
  rw [List.drop_eq_getElem_cons hi, List.filterMap_cons, h]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-! ## The frozen messages -/

/-- **A `Ready`'s message frozen** (persistent): read-only at a content without unknown fields in
its snapshot's conf state, which is the message's. -/
def frozenMsg (l : Loc) (st : MsgSt) : IProp GF :=
  iprop(∃ c : MsgC, msgPtsCC l DFrac.discard DFrac.discard false c ∗ ⌜c.model = st ∧ c.csUfNil⌝)

instance frozenMsg_persistent (l : Loc) (st : MsgSt) : Persistent (frozenMsg (GF := GF) l st) := by
  unfold frozenMsg; infer_instance

theorem frozenMsg_ptsC (l : Loc) (st : MsgSt) :
    frozenMsg (GF := GF) l st ⊢ msgPtsC l DFrac.discard DFrac.discard false st := by
  unfold frozenMsg
  iintro ⟨%c, #Hc, %H⟩
  rw [← H.1]
  iapply msgPtsCC_msgPtsC _ _ _ _ c H.2
  iexact Hc

theorem msgOwnZ_frozen (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOwnZ (GF := GF) false l dq st ⊢ |==> frozenMsg l st := by
  unfold msgOwnZ frozenMsg
  iintro ⟨%c, Hc, %H⟩
  imod msgPtsCC_persist _ _ _ $$ Hc with Hc
  imodintro
  iexists c
  iframe Hc
  ipureintro; exact ⟨H.1, H.2.1.1⟩

theorem bigSepL_frozen : ∀ (L : List QMsg),
    ([∗list] q ∈ L, msgOwnZ (GF := GF) false q.loc (readyDq q.st) q.st) ⊢
      |==> [∗list] q ∈ L, frozenMsg (GF := GF) q.loc q.st
  | [] => by
    iintro -
    imodintro
    iapply (BigSepL.bigSepL_nil (Φ := fun _ (q : QMsg) => frozenMsg (GF := GF) q.loc q.st)).2
    iempintro
  | a :: L => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, Hl⟩
    imod msgOwnZ_frozen _ _ _ $$ Ha with #Ha
    imod bigSepL_frozen L $$ Hl with Hl
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Ha Hl

/-! ## The loop head's rest, opened for the reports -/

theorem nodeMemB1_emit (n : Loc) : nodeMemB1 (GF := GF) n ⊢ emitOk n ∗ (emitOk n -∗ nodeMemB1 n) := by
  iintro H
  iunfold nodeMemB1 at H
  icases H with ⟨%mhs, %rhs, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, He⟩
  iframe He
  iintro He
  iunfold nodeMemB1
  iexists mhs, rhs
  iframe

theorem nodeRaft_tlb (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG)) (γ : AntNames)
    (j : Fin γ.R.N) (rs : RNState) :
    nodeRaft (GF := GF) γ j rs ⊢ □ rnTermLB γ.raft rs.tc ∗ nodeRaft γ j rs := by
  haveI := h_tlp γ.raft rs.tc
  iintro H
  iunfold nodeRaft at H
  icases H with ⟨%x, %g, Hgv, Hsf, Hdg, #Htlb, Hbud, %Hγ⟩
  iframe Htlb
  iunfold nodeRaft
  iexists x, g
  iframe Hgv Hsf Hdg Htlb Hbud
  ipureintro; exact Hγ

/-- **`loopRest` opened for a report**: the right to report, the cause cell against the view, the
view's fragment, the sent lists' lower bounds, the term ceiling's lower bound; closed again at a
view with the same disk, liveness, role, delivered entries, reads and configuration. -/
theorem loopRest_open (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG)) (γ : AntNames)
    (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) (net : List Msg) (xnet : List XMsg)
    (rs : RNState) :
    loopRest (GF := GF) γ j n v net xnet rs ⊢ ∃ cl : Loc,
      emitOk n ∗ n.[H.node, go!"cause"] ↦ cl ∗ causeOwn γ j v cl ∗ viewFrag γ j v ∗ nodeLive γ j ∗
      sentLb γ net ∗ xsentLb γ xnet ∗ □ rnTermLB γ.raft rs.tc ∗
      (∀ (v' : AntSim.NodeView) (net' : List Msg) (xnet' : List XMsg) (cl' : Loc),
        ⌜v'.dur = v.dur ∧ v'.alive = v.alive ∧ AntSim.roleS v' = AntSim.roleS v ∧
          v'.delivered = v.delivered ∧ v'.reads = v.reads ∧ v'.conf = v.conf⌝ -∗
        emitOk n -∗ n.[H.node, go!"cause"] ↦ cl' -∗ causeOwn γ j v' cl' -∗ viewFrag γ j v' -∗
        nodeLive γ j -∗ sentLb γ net' -∗ xsentLb γ xnet' -∗ loopRest γ j n v' net' xnet' rs) := by
  iintro Hrest
  iunfold loopRest at Hrest
  icases Hrest with ⟨%d, %ms, %hsl, %cl, %csl, %role, %applied, %si, #Hd, Hmem, Hms, Hrole, Hhs,
    Hcause, Happ, Hconf, Hv, Hl, Hdisk, Hstor, %Hsto, Hnr, %Hpv, #Hhsro, #Hcs, #Hrq, %Hc0, #Hlb,
    #Hxlb, Hco⟩
  icases nodeMemB1_emit n $$ Hmem with ⟨Hemit, Hmemc⟩
  icases nodeRaft_tlb h_tlp γ j rs $$ Hnr with ⟨#Htlb, Hnr⟩
  iexists cl
  iframe Hemit Hcause Hco Hv Hl Hlb Hxlb Htlb
  iintro %v' %net' %xnet' %cl' %Heq Hemit Hcause Hco Hv Hl #Hlb' #Hxlb'
  obtain ⟨hd, ha, hr, hdl, hrd, hc⟩ := Heq
  ihave Hmem := Hmemc $$ Hemit
  iunfold loopRest
  iexists d, ms, hsl, cl', csl, role, applied, si
  rw [hd, show readsOwn (GF := GF) γ v' = readsOwn γ v by unfold readsOwn; rw [hrd]]
  iframe Hd Hmem Hms Hrole Hhs Hcause Happ Hconf Hv Hl Hdisk Hstor Hnr Hhsro Hcs Hrq Hlb' Hxlb' Hco
  isplitr
  · ipureintro; exact Hsto
  isplitr
  · ipureintro; exact ⟨by rw [ha]; exact Hpv.1, by rw [hr]; exact Hpv.2.1, by rw [hdl]; exact Hpv.2.2⟩
  ipureintro; rw [hc]; exact Hc0

/-- **The pending messages' facts at the iteration's first view** (`drain_peekB1` through
`drainMidB1`). -/
theorem drainMid_peek (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (np bp rdp n : Loc) (γ : AntNames) (j : Fin γ.R.N) (I : DrainIterB1) (vv : AntSim.NodeView)
    (net : List Msg) (xnet : List XMsg) :
    inv antN (antInv (GF := GF) γ) ∗ drainMidB1 np bp rdp n γ j I vv net xnet ⊢
      |={⊤}=> ⌜∃ (S : AntCheck.State) (net' : List Msg), AntSim.NodeOk γ.R γ.dec S net' j vv⌝ ∗
        drainMidB1 np bp rdp n γ j I vv net xnet := by
  iintro ⟨#Hinv, Hmid⟩
  iunfold drainMidB1 at Hmid
  icases Hmid with ⟨Hnp, Hbp, Hrdp, Hrn, Hraw, Hrest, Hdur, Hce, Hrs, Hrsok, %Hv⟩
  icases loopRest_open h_tlp γ j n vv net xnet I.rs₂ $$ Hrest with
    ⟨%cl, Hemit, Hcause, Hco, Hvf, Hl, #Hlb, #Hxlb, #Htlb, Hclose⟩
  imod drain_peekB1 h_vu h_lo γ j vv $$ [$Hinv $Hvf $Hl] with ⟨%Hpk, Hvf, Hl⟩
  ihave Hrest := Hclose $$ %vv %net %xnet %cl [] Hemit Hcause Hco Hvf Hl Hlb Hxlb
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  imodintro
  isplitr
  · ipureintro; exact Hpk
  iunfold drainMidB1
  iframe Hnp Hbp Hrdp Hrn Hraw Hrest Hdur Hce Hrs Hrsok
  ipureintro; exact Hv

/-- The cause cell after the cause's report: `nil`, nothing pending. -/
theorem causeOwn_told (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView)
    (h : v.byE = go!"recv" → v.told = true) : ⊢ causeOwn (GF := GF) γ j v null := by
  unfold causeOwn
  rw [if_neg (fun hp => by rw [h hp.1] at hp; cases hp.2)]
  iunfold pendingCause
  ileft
  ipureintro; exact ⟨rfl, rfl⟩

end proof

/-! ## The send loop -/

attribute [-instance] pure_wp_slice_for_range

section send
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

set_option maxHeartbeats 4000000 in
/-- **`drainSendB1.stmt`**: the range loop at the invariant "the first `i` messages sent": `drainMidB1`
at a view whose pending protocol and transfer messages are the `Ready`'s from the `i`th on. -/
theorem drainSendB1
    (h_vu : view_update.law (GF := GF))
    (h_lo : nodeLive_over.law (GF := GF))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (h_le : rnTermLB_le.law (GF := GF) (hG := hG))
    (wp_reportCause : node.reportCause.spec (GF := GF) (hG := hG))
    (wp_sendEv : node.sendEv.spec (GF := GF) (hG := hG))
    (wp_emit : node.emit.spec (GF := GF) (hG := hG))
    (wp_sendMsg : node.sendMsg.spec (GF := GF) (hG := hG)) :
    drainSendB1.stmt (GF := GF) (hG := hG) := by
  intro hTB np bp rdp ep c n γ j I v₁ net₁ xnet₁ qp K Φ hp1 hx1
  iintro ⟨#Hpkg, #Hc, #Hn, %Hb1, Hmid, Hmsgs, Hep, Hadd, Htt, HΦ⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop,
    #Hbc, #Hnj, #Hmu, #Hinv, %Hfits, #Hpm, #Hrdm, #Hasi, %Hnames⟩
  obtain ⟨hs, hcc, hfw, has⟩ := rMd_flags_d Hmode.2 Hb1
  have hinm : ∀ S V net xnet, AntSim.AntSim γ.R γ.dec S V net xnet →
      AntSim.InMask AntSim.mskB1 γ.R net xnet := by
    intro S V net xnet hA
    obtain ⟨-, -, -, -, hmd', hdrv⟩ := Hmode.2
    obtain ⟨hb', has', hp', hs', -, hr', hsn', hcc', hfw', -⟩ := Hb1
    refine inMask_b1_of ?_ ?_ ?_ ?_ ?_ hA
    · rw [hmd']; exact rnLe_scopeMd_b1 _ _ hfw' has' hsn' hcc'
    · rw [hdrv]; exact hb'
    · rw [hdrv]; exact hp'
    · rw [hdrv]; simp [modeDrv, hs']
    · rw [hdrv]; exact hr'
  have hss : γ.mode.SnapStatus' = false := Hb1.2.2.2.2.1
  have hfwd : γ.mode.Forward' = false := by
    obtain ⟨-, -, -, -, -, -, hf7, -⟩ := Hmode.1
    obtain ⟨-, -, -, -, -, -, -, -, hsf, -⟩ := Hb1
    cases h : γ.mode.Forward'
    · rfl
    · have := hf7 h; rw [hsf] at this; cases this
  -- the pending messages' facts, at the first view
  imod drainMid_peek h_vu h_lo h_tlp np bp rdp n γ j I v₁ net₁ xnet₁ $$ [$Hinv $Hmid] with
    ⟨%Hpk, Hmid⟩
  obtain ⟨S₀, netS, hok0⟩ := Hpk
  obtain ⟨hpk, hxk⟩ := pendFacts_of hok0
  -- the messages frozen
  iunfold drainMsgsB1 at Hmsgs
  icases Hmsgs with ⟨Hsl, Hcap, Hown, #Hrm, %Hmok⟩
  imod bigSepL_frozen I.ms $$ Hown with #Hfz
  -- the iteration's facts
  iunfold drainMidB1 at Hmid
  icases Hmid with ⟨Hnp, Hbp, Hrdp, Hrn, Hraw, Hrest, Hdur, Hce, Hrs, Hrsok, %Hv⟩
  obtain ⟨-, -, -, -, -, -, hax, hxr, htrf, -, htc, -⟩ := Hv.2.2.2.2.2.2.2
  have hnsnap : ∀ m ∈ I.ms, m.st.msg.Type' ≠ MsgSnap := by
    intro m hm
    rcases hax m hm with h | h
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 h
      have hq1 : q ∈ v₁.pend := by rw [hp1]; exact List.mem_filterMap.2 ⟨m, hm, hq⟩
      exact (absMsgOf_st hq (pend_ne_snap (hpk q hq1).1 hs)).1
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
      exact xmsgOf_ne_snap hx
  unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.drain.sendE
  icases typedPointsto_not_null_dup _ _ _ $$ Hrdp with ⟨Hrdp, %Hrnn⟩
  iStructNamed Hrdp
  wp_pure
  wp_auto
  ihave Hrdp : (rdp ↦ I.rd : IProp GF) $$ [SoftState HardState ReadStates Entries Snapshot
      CommittedEntries Messages MustSync]
  · iapply typedPointsto_combine _ _ _ Hrnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply (wp_slice_range_ro (V := Loc) _ I.rd.Messages' (I.ms.map QMsg.loc) (DFrac.own 1) _
    (fun i => iprop(∃ (vv : AntSim.NodeView) (net : List Msg) (xnet : List XMsg) (x : Loc),
      drainMidB1 np bp rdp n γ j I vv net xnet ∗
      ⌜vv.pend = (I.ms.drop i).filterMap (fun m => absMsgOf m.st) ∧
        vv.xpend = (I.ms.drop i).filterMap (fun m => xmsgOf m.st)⌝ ∗
      m_ptr ↦ x ∗ ep ↦ false ∗ netAdder c γ qp ∗ threadTok)))
    $$ Hsl [Hnp Hbp Hrdp Hrn Hraw Hrest Hdur Hce Hrs Hrsok m Hep Hadd Htt]
  · iexists v₁, net₁, xnet₁, _
    simp only [List.drop_zero]
    iframe m Hep Hadd Htt
    isplitl
    · iunfold drainMidB1
      iframe
      ipureintro; exact Hv
    ipureintro; exact ⟨hp1, hx1⟩
  · imodintro
    iintro %i %x %hx HP Hs
    icases HP with ⟨%vv, %net, %xnet, %x0, Hmid, %Hpx, Hm, Hep, Hadd, Htt⟩
    have hi : i < I.ms.length := by
      have := (List.getElem?_eq_some_iff.1 hx).1; simpa using this
    have hxe : x = I.ms[i].loc := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi] at hx
      exact (Option.some.inj hx).symm
    subst hxe
    have hmem : I.ms[i] ∈ I.ms := List.getElem_mem hi
    obtain ⟨hT, hN, hS⟩ := Hmok I.ms[i] hmem
    have hterm : uint.Z I.ms[i].st.msg.Term' < 2 ^ 61 := by omega
    have hns' : I.ms[i].st.msg.Type' ≠ MsgSnap := hnsnap _ hmem
    ihave #Hrq := BigSepL.bigSepL_lookup (Φ := fun _ q => isRaftMsg (GF := GF) γ.raft.raftNames
      (AntSim.nodeId j) q.st) (List.getElem?_eq_getElem hi) $$ Hrm
    ihave #Hfq := BigSepL.bigSepL_lookup (Φ := fun _ q => frozenMsg (GF := GF) q.loc q.st)
      (List.getElem?_eq_getElem hi) $$ Hfz
    ihave %Hsent := isRaftMsg_shape_s γ.raft.raftNames (AntSim.nodeId j) I.ms[i].st $$ Hrq
    ihave %Hres := isRaftMsg_resps γ.raft.raftNames (AntSim.nodeId j) I.ms[i].st $$ Hrq
    have hnorm : AllNormal I.ms[i].st.ents := by
      rcases hq : absMsgOf I.ms[i].st with _ | q
      · rcases hax _ hmem with h | h
        · rw [hq] at h; cases h
        · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
          have hxe := Hsent.2.2.2.2.2.2.1 (by rcases (xmsgOf_type hx).1 with h' | h' <;> simp [h'])
          intro e he; rw [hxe.1] at he; cases he
      · have hq1 : q ∈ v₁.pend := by rw [hp1]; exact List.mem_filterMap.2 ⟨_, hmem, hq⟩
        have hns : q.ty ≠ .snap := pend_ne_snap (hpk q hq1).1 hs
        rw [(absMsgOf_st hq hns).2]
        exact (hpk q hq1).1.1 hcc
    iunfold drainMidB1 at Hmid
    icases Hmid with ⟨Hnp, Hbp, Hrdp, Hrn, Hraw, Hrest, Hdur, Hce, Hrs, Hrsok, %Hvv⟩
    have hby : vv.byE = I.v.byE := Hvv.2.2.2.2.1
    icases loopRest_open h_tlp γ j n vv net xnet I.rs₂ $$ Hrest with
      ⟨%cl, Hok, Hcl, Hco, Hvf, Hl, #Hlb, #Hxlb, #Htlb, Hclose⟩
    ihave Hrep := causeOwn_report h_vu h_lo c γ j vv net xnet cl
      (iprop(∃ (b : Bool) (net₂ : List Msg) (xnet₂ : List XMsg),
        ⌜(vv.byE = go!"recv" → b = true) ∧ net <+: net₂ ∧ xnet <+: xnet₂⌝ ∗ sentLb γ net₂ ∗
          xsentLb γ xnet₂ ∗ viewFrag γ j { vv with told := b } ∗ nodeLive γ j)) hinm
      $$ [Hco Hvf Hl]
    · iframe Hc Hlb Hxlb Hco Hvf Hl
      iintro %b %net₂ %xnet₂ %Hb Hlb2 Hxlb2 Hvf Hl
      iexists b, net₂, xnet₂
      iframe Hlb2 Hxlb2 Hvf Hl
      ipureintro; exact Hb
    icases Hrep with ⟨%o, Hpc, Hrep⟩
    ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    wp_auto
    wp_apply +noauto wp_reportCause c γ n j cl o _ $$ [$Hpkg $Hc $Hn $Hok $Hcl $Hpc $Hrep]
      as ⟨Hok, Hcl, Hrep⟩
    icases Hrep with ⟨%b, %net₂, %xnet₂, %Hb, #Hlb2, #Hxlb2, Hvf, Hl⟩
    wp_take_receipt as Hr2
    ihave HpC := frozenMsg_ptsC _ _ $$ Hfq
    wp_apply +noauto wp_sendEv c γ n j I.v.byE I.ms[i].loc DFrac.discard DFrac.discard false
      I.ms[i].st hns' hnorm $$ [$Hpkg $Hc $Hn $HpC] as %p ⟨-, Hev, Hr3⟩
    wp_take_receipt as Hr4
    have hvvt : ({ vv with told := b } : AntSim.NodeView).byE = I.v.byE := hby
    have htold : AntSim.Told ({ vv with told := b } : AntSim.NodeView) := fun h => Hb.1 h
    haveI := h_tlp γ.raft I.ms[i].st.msg.Term'
    ihave #Htq := h_le γ.raft I.rs₂.tc I.ms[i].st.msg.Term' hT $$ Htlb
    ihave HpC2 := frozenMsg_ptsC _ _ $$ Hfq
    rcases habs : absMsgOf I.ms[i].st with _ | q
    · -- a transfer message
      obtain ⟨x, hx⟩ : ∃ x, xmsgOf I.ms[i].st = some x := by
        rcases hax _ hmem with h | h
        · rw [habs] at h; cases h
        · exact Option.isSome_iff_exists.1 h
      obtain ⟨hxo, hxz⟩ := hxr _ hmem x hx
      have htr : γ.R.md.transfer = true := by
        cases h : γ.R.md.transfer
        · have := htrf h _ hmem; rw [habs] at this; cases this
        · rfl
      have hxm : x ∈ v₁.xpend := by rw [hx1]; exact List.mem_filterMap.2 ⟨_, hmem, hx⟩
      obtain ⟨-, hdst, -, -⟩ := hxk x hxm
      have hxt := xmsgOf_type hx
      have hents : I.ms[i].st.ents = [] :=
        (Hsent.2.2.2.2.2.2.1 (by rcases hxt.1 with h' | h' <;> simp [h'])).1
      have hxterm : uint.Z x.term < 2 ^ 61 := by rw [hxt.2]; exact hterm
      obtain ⟨xrest, hxrest⟩ : ∃ xrest, xrest = (I.ms.drop (i + 1)).filterMap (fun m => xmsgOf m.st) :=
        ⟨_, rfl⟩
      have hxpend' : ({ vv with told := b } : AntSim.NodeView).xpend = x :: xrest := by
        show vv.xpend = _
        rw [Hpx.2, hxrest]; exact filterMap_drop_some (f := fun m => xmsgOf m.st) hi hx
      ihave Hrc : ⧗ (AntSim.evSendX (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE
          x).weight $$ [Hr2 Hr4]
      · rw [evSendX_weight]
        iapply (receipt_add (GF := GF) 1 1).2
        iframe Hr2 Hr4
      ihave #Hext0 := factsExt_none (GF := GF) γ
      ihave Hrep := report_upd h_vu h_lo c γ j { vv with told := b }
        (sendXView { vv with told := b } xrest)
        (AntSim.evSendX (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE x)
        net₂ [] xnet₂ [x] (fun G0 G => G = G0)
        (iprop(viewFrag γ j (sendXView { vv with told := b } xrest) ∗ nodeLive γ j ∗
          (∃ (net : List Msg) (xnet : List XMsg), sentLb γ net ∗ xsentLb γ xnet ∗
            ⌜net₂ <+: net ∧ (∀ m ∈ ([] : List Msg), m ∈ net) ∧ xnet₂ <+: xnet ∧
              ∀ y ∈ [x], y ∈ xnet⌝)))
        (evSendX_numsOk hxterm _ _) (evSendX_chgOk _ _ _)
        (sendXHstep j _ x xrest net₂ xnet₂ hinm has hxpend' htold) $$ [Hvf Hl Hrc]
      · iframe Hc Hlb2 Hxlb2 Hext0 Hrc Hvf Hl
        iintro H; iexact H
      have hev : atNode (AntSim.nameOf (AntSim.nodeId j)) (sendEvM I.v.byE I.ms[i].st) =
          AntSim.evSendX (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE x := by
        rw [hvvt]; exact sendEvM_x hx hxz hents hterm _ _
      wp_apply +noauto wp_emit c γ n j p (sendEvM I.v.byE I.ms[i].st) _
        $$ [$Hpkg $Hc $Hn $Hok $Hev Hrep] as ⟨Hok, Hrep⟩
      · rw [hev]; iexact Hrep
      icases Hrep with ⟨Hvf, Hl, %net₃, %xnet₃, #Hlb3, #Hxlb3, %Hn3⟩
      ihave Hsf : sendFacts (GF := GF) γ I.ms[i].st $$ []
      · iapply sendFacts_of_x γ (AntSim.nodeId j) I.ms[i].st x
          (xnetFacts_of_ready hx hxo Hsent htr hdst ⟨j, rfl⟩ (hS x hx) hterm hxz)
        iframe Hrq Htq
        iapply xsentW_of_lb γ xnet₃ x (Hn3.2.2.2 x List.mem_cons_self)
        iexact Hxlb3
      try wp_auto
      wp_apply wp_sendMsg c γ n j I.ms[i].loc false I.ms[i].st qp
        $$ [$Hpkg $Hc $Hn $Hok $Hadd $Htt $HpC2 $Hsf] as ⟨Hok, Hadd, Htt, -⟩
      · ipureintro; exact ⟨hss, Hres⟩
      isplitr
      · ipureintro; rfl
      iframe Hs
      ihave Hco := causeOwn_told (GF := GF) γ j (sendXView { vv with told := b } xrest) Hb.1
      ihave Hrest := Hclose $$ %(sendXView { vv with told := b } xrest) %net₃ %xnet₃ %null []
        Hok Hcl Hco Hvf Hl Hlb3 Hxlb3
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      iexists sendXView { vv with told := b } xrest, net₃, xnet₃, I.ms[i].loc
      iframe Hm Hep Hadd Htt
      isplitl
      · iunfold drainMidB1
        iframe Hnp Hbp Hrdp Hrn Hraw Hrest Hdur Hce Hrs Hrsok
        ipureintro; exact Hvv
      ipureintro
      exact ⟨by show vv.pend = _; rw [Hpx.1]; exact filterMap_drop_none (f := fun m => absMsgOf m.st) hi habs,
        hxrest⟩
    · -- a protocol message
      have hq1 : q ∈ v₁.pend := by rw [hp1]; exact List.mem_filterMap.2 ⟨_, hmem, habs⟩
      obtain ⟨hmq, hpq⟩ := hpk q hq1
      have hns : q.ty ≠ .snap := pend_ne_snap hmq hs
      have hnums := hN q habs
      have hxn : xmsgOf I.ms[i].st = none := xmsgOf_none_of_absMsgOf (by rw [habs]; rfl)
      obtain ⟨rest, hrest⟩ : ∃ rest, rest = (I.ms.drop (i + 1)).filterMap (fun m => absMsgOf m.st) :=
        ⟨_, rfl⟩
      have hpend' : ({ vv with told := b } : AntSim.NodeView).pend = q :: rest := by
        show vv.pend = _
        rw [Hpx.1, hrest]; exact filterMap_drop_some (f := fun m => absMsgOf m.st) hi habs
      ihave #Hmsg := isRaftMsg_isMessage_s γ.raft.raftNames (AntSim.nodeId j) I.ms[i].st q habs hns
        $$ Hrq
      ihave #Hext := sendExt_b1 γ q $$ Hmsg
      ihave Hrc : ⧗ (AntSim.evSend (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE
          q).weight $$ [Hr2 Hr3 Hr4]
      · rw [evSend_weight habs hns]
        iapply (receipt_add (GF := GF) (I.ms[i].st.ents.length + 1) 1).2
        iframe Hr4
        iapply (receipt_add (GF := GF) I.ms[i].st.ents.length 1).2
        iframe Hr3 Hr2
      ihave Hrep := report_upd h_vu h_lo c γ j { vv with told := b }
        (sendView { vv with told := b } rest)
        (AntSim.evSend (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE q)
        net₂ [q] xnet₂ [] (fun G0 G => FactsLe γ.R G0 G ∧ AntSim.RaftLaws G ∧ AntSim.MsgFacts G q)
        (iprop(viewFrag γ j (sendView { vv with told := b } rest) ∗ nodeLive γ j ∗
          (∃ (net : List Msg) (xnet : List XMsg), sentLb γ net ∗ xsentLb γ xnet ∗
            ⌜net₂ <+: net ∧ (∀ m ∈ [q], m ∈ net) ∧ xnet₂ <+: xnet ∧
              ∀ y ∈ ([] : List XMsg), y ∈ xnet⌝)))
        (evSend_numsOk habs hns hnums hterm _ _) (evSend_chgOk _ _ _)
        (sendHstep j _ q rest net₂ xnet₂ hinm has hpend' htold (fun _ => hN q habs)) $$ [Hvf Hl Hrc]
      · iframe Hc Hlb2 Hxlb2 Hext Hrc Hvf Hl
        iintro H; iexact H
      have hev : atNode (AntSim.nameOf (AntSim.nodeId j)) (sendEvM I.v.byE I.ms[i].st) =
          AntSim.evSend (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE q := by
        rw [hvvt]; exact sendEvM_abs habs hns hnums hterm _ _
      wp_apply +noauto wp_emit c γ n j p (sendEvM I.v.byE I.ms[i].st) _
        $$ [$Hpkg $Hc $Hn $Hok $Hev Hrep] as ⟨Hok, Hrep⟩
      · rw [hev]; iexact Hrep
      icases Hrep with ⟨Hvf, Hl, %net₃, %xnet₃, #Hlb3, #Hxlb3, %Hn3⟩
      ihave Hsf : sendFacts (GF := GF) γ I.ms[i].st $$ []
      · by_cases hprop : q.ty = .propose
        · iunfold sendFacts
          ileft
          ipureintro
          obtain ⟨ty, hty, hqe⟩ := absMsgOf_cases_s habs hns
          refine ⟨mtypeOf_propose_s ?_, hfwd⟩
          rw [hty, ← hprop, hqe]; rfl
        · iapply sendFacts_of γ (AntSim.nodeId j) I.ms[i].st q habs hns
            (netFacts_of_pend habs hmq hpq hprop Hsent hnums hterm hs hfw hcc)
          iframe Hrq Htq
          iapply sentW_of_lb γ net₃ q (Hn3.2.1 q List.mem_cons_self)
          iexact Hlb3
      try wp_auto
      wp_apply wp_sendMsg c γ n j I.ms[i].loc false I.ms[i].st qp
        $$ [$Hpkg $Hc $Hn $Hok $Hadd $Htt $HpC2 $Hsf] as ⟨Hok, Hadd, Htt, -⟩
      · ipureintro; exact ⟨hss, Hres⟩
      isplitr
      · ipureintro; rfl
      iframe Hs
      ihave Hco := causeOwn_told (GF := GF) γ j (sendView { vv with told := b } rest) Hb.1
      ihave Hrest := Hclose $$ %(sendView { vv with told := b } rest) %net₃ %xnet₃ %null []
        Hok Hcl Hco Hvf Hl Hlb3 Hxlb3
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      iexists sendView { vv with told := b } rest, net₃, xnet₃, I.ms[i].loc
      iframe Hm Hep Hadd Htt
      isplitl
      · iunfold drainMidB1
        iframe Hnp Hbp Hrdp Hrn Hraw Hrest Hdur Hce Hrs Hrsok
        ipureintro; exact Hvv
      ipureintro
      exact ⟨hrest, by show vv.xpend = _; rw [Hpx.2]; exact filterMap_drop_none (f := fun m => xmsgOf m.st) hi hxn⟩
  iintro ⟨%vv, %net, %xnet, %x, Hmid, %Hpx, Hm, Hep, Hadd, Htt⟩ Hs
  rw [List.length_map, List.drop_length] at Hpx
  wp_auto
  iapply HΦ
  iframe Hmid Hep Hadd Htt
  isplitr
  · ipureintro; exact Hpx
  iunfold drainSentB1
  iframe Hs
  ihave Hall := (BigSepL.bigSepL_mono (Φ := fun _ (q : QMsg) => frozenMsg (GF := GF) q.loc q.st)
    (Ψ := fun _ (q : QMsg) => msgPtsC (GF := GF) q.loc DFrac.discard DFrac.discard false q.st)
    (l := I.ms) (fun _ => frozenMsg_ptsC _ _)) $$ Hfz
  iframe Hall
  ipureintro; exact hnsnap

end send

end AntHarness
end EtcdGrove
end Perennial
