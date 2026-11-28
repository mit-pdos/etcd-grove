/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__step.lean`: a message of the
network to node `j` (a protocol message, `netMsg`, or a transfer message, `netXMsg`), in a run of
B1's mask (no batching: `batch` false; no snapshots: `snap` false; no forwarding: `prop` false). Its
report made (`msgOf`) into the cause cell (`causeOwn_recv`/`causeOwn_recvX`, the receipts of the
resolutions before `rn.Step`), the term ceiling raised over the message's (`rnBudget_step`, one more
for a `MsgTimeoutNow`), a stepped `MsgReadIndex`'s read credit minted (`rdCred_of_receipt`),
`RawNode.Step` at `γ.R.md`, the view noted (`view_input`); the loop head: the unchanged arm
(`errStepPeer`, a response from a non-voter) by `Reach.stay`, otherwise `Reach.input` (`.recv m`:
`RecvEndR`; `.recvX x`: `TimeoutNowEndR`/`TransferRecvEndR`, a `MsgTimeoutNow`'s term at most the
receiver's disk's by `nodeOwn_acked`, raft's `isAcked_term_le`); the drain (`input`, by `recv`), the cell reset
(`nodeOwn_drained_reset`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__step
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__input
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.msgOf
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessStep
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.CloneMsgLaw
public import Proof.ReceiptTactics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.step.wp_proof
    (wp_Step : RawNode.Step.apiSpec (GF := GF) (hG := hG))
    (wp_input : node.input.spec (GF := GF) (hG := hG))
    (wp_msgOf : msgOf.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_tc : rawNode_term_tc.law (GF := GF) (hG := hG))
    (h_raise : rawNode_raise_tc.law (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_bstep : rnBudget_step.law (GF := GF) (hG := hG))
    (h_vu : view_update.law (GF := GF) (hG := hG))
    (h_lo : nodeLive_over.law (GF := GF) (hG := hG))
    (msk : AntSim.SimMask) (h_quiet : antSim_quiet_in.law msk) (h_mask : runInMask.law msk)
    (h_tr : msk.md.transfer = true) :
    node.step.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v q ml st
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, %Hb1, Hm⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  have Hbatch : γ.mode.Batch' = false := Hb1.1
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm, #Hrdm, #Hasi, %Hnames⟩
  iunfold clusterRO at Hro
  icases Hro with ⟨%nsl, %ivl, #Hns, #Hnsl, %HN, #Hmd, #Hiv, #Hivs⟩
  ihave Hmd' := Hmd
  iStructNamed Hmd'
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, %d, #Hnc, #Hid, #Hname, #Hin, #Hbag, #Hd, #Hlog⟩
  obtain ⟨hs, hcc, hfw, has⟩ := rMd_flags Hmode.2 Hb1
  icases Hm with (⟨%m, Hnm, %Hd⟩ | ⟨%x, Hnx, %Hd⟩)
  · -- a protocol message
    iunfold netMsg at Hnm
    icases Hnm with ⟨⟨%cm, Hm, %Hcm⟩, %Hnf, #Hism, Htlb, #Hsent⟩
    obtain ⟨hmod, hcs⟩ := Hcm
    have hrd := msgPtsCC_readE (GF := GF) ml (needsCap st.msg) cm hcs DFrac.discard DFrac.discard
    rw [discard_op_discard, hmod] at hrd
    icases hrd $$ Hm with ⟨Hmh, Hmb⟩
    icases nodeOwn_idle_open h_bp c γ j n v $$ Hown with
      ⟨%rn, %rs, Hrnf, Hraw, Htc, #Hb, %Hst, Hcause, Hv, Hl, %Hpr, Hclose⟩
    obtain ⟨hrv, hI, hP, hN, hk⟩ := Hpr
    icases h_wf γ.R.md hs hcc hfw has _ _ _ _ _ _ _ $$ Hraw with ⟨%Hwf, Hraw⟩
    icases h_tc γ.R.md hs hcc hfw has _ _ _ _ _ _ _ $$ Hraw with ⟨%Htcle, Hraw⟩
    have hns := netFacts_ne_snap Hnf hs hfw
    have hnp := netFacts_ne_prop Hnf hs hfw
    have hnt := netFacts_ne_timeoutNow Hnf hs hfw
    have hto : st.msg.To' = AntSim.nodeId j := by rw [← absMsgOf_dst Hnf.2.2.2.2.1, Hd]
    obtain ⟨ty0, hty0, -, hm0, huniq, -⟩ := netFacts_absMsg Hnf hs hfw
    have hsrc : m.src = st.msg.From' := by rw [← hm0]; rfl
    wp_take_receipt as Hr1
    wp_apply +noauto wp_GetType.1 ml _ _ _ st $$ [$Hpb $Hmh] as Hmh
    rw [Hbatch]
    wp_take_receipt as Hr2
    wp_apply +noauto wp_GetType.1 ml _ _ _ st $$ [$Hpb $Hmh] as Hmh
    wp_take_receipt as Hr3
    wp_apply +noauto wp_msgOf ml _ _ _ st (AntSim.nodeId j) γ.mode.Nodes' hns Hnf.2.2.2.1
      $$ [$Hpkg $Hmh] as %g ⟨Hmh, #Hg, Hrm⟩
    ihave Hm := Hmb $$ Hmh
    wp_take_receipt as Hr4
    icases typedPointsto_not_null_dup _ _ _ $$ cause with ⟨cause, %Hcnn⟩
    ihave Hrb := receipt_ite (GF := GF) (st.msg.Type' = MsgTimeoutNow) $$ Hr4
    imod h_bstep γ.raft rs.tc st.msg.Term' (st.msg.Type' = MsgTimeoutNow) ⊤ (by solve_ndisj)
      $$ Hb Htc Htlb Hrb with ⟨%Hbd, %tb, Htb, %Hle⟩
    have htt : uint.Z rs.term ≤ uint.Z rs.tc := by rw [← Hwf.2.2]; exact Htcle
    have hle1 : uint.Z rs.tc ≤ uint.Z tb := by split at Hle <;> omega
    have hle2 : uint.Z st.msg.Term' ≤ uint.Z tb := by split at Hle <;> omega
    ihave Hraw := h_raise γ.R.md hs hcc hfw has _ _ _ _ _ _ _ tb hle1 $$ Hraw
    imod rdCred_of_receipt (GF := GF) γ st $$ Hrdm Hr3 with Hcr
    ihave Hm' : (∃ c : MsgC, msgPtsCC ml (DFrac.own 1) DFrac.discard (needsCap st.msg) c ∗
        ⌜c.model = st ∧ c.csUfNil ∧ (∀ b, γ.raft.raftNames.maxData = some b →
          st.msg.Type' ≠ MsgSnap → msgSizeOk c)⌝) $$ [Hm]
    · iexists cm; iframe Hm; ipureintro
      exact ⟨hmod, hcs, fun b hb => by rw [Hst.2.2] at hb; cases hb⟩
    ihave #Hxfer : □ (⌜st.msg.Type' = MsgTransferLeader ∧ st.msg.Term' ≠ W64 0⌝ -∗
        isLeader γ.raft.raftNames (AntSim.nodeId j) st.msg.Term') $$ []
    · imodintro; iintro %h; iexfalso; ipureintro; exact netFacts_ne_transfer Hnf hs hfw h.1
    ihave #Hmsg : □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
        isMessage γ.raft.raftNames (absMsg ty st.msg st.ents st.ctx)) $$ []
    · imodintro; iintro %ty %hty' %-
      rw [huniq ty hty', hm0]; iexact Hism
    have hnok : NetMsgOk (AntSim.nodeId j) st := hto ▸ Hnf.1
    wp_apply +noauto wp_Step γ.R.md hs hcc hfw has γ.raft.raftNames rn (AntSim.nodeId j)
        { rs with tc := tb } v.r [] v.r.p.log.length ml st hnok
        (fun md' hmd => by
          subst hmd
          refine ⟨netTypes_sub_stepTypes Hnf.2.1, fun hr h => Hnf.2.2.1 hr (.inr h), fun hnv => ?_,
            fun h => (netFacts_ne_transfer Hnf hs hfw h).elim⟩
          obtain ⟨i, hi⟩ := Hnf.2.2.2.2.2.2.1
          rw [Hst.2.1, ← hsrc, hi]
          exact nodeId_mem_voters0 Hmode.1 Hmode.2 hnv i)
        hle2 (fun h => absurd h hnt) hrv.2.2.2.2.2.1 Hst.1
        $$ [$Hrpkg $Hraw $Hm' $Hxfer $Hmsg Hcr] as %err %t %r' %ip' ⟨Hraw, %Ht, %Hend⟩
    · isplitr
      · imodintro; iintro %h; iexfalso; ipureintro; exact hns h
      · iexact Hcr
    ihave #Hsw : □ (∀ m', ⌜AntSim.Input.recv m = .recv m'⌝ -∗ sentW (GF := GF) γ m') $$ []
    · imodintro; iintro %m' %h; cases h; iexact Hsent
    ihave #Hsx : □ (∀ x, ⌜AntSim.Input.recv m = .recvX x⌝ -∗ xsentW (GF := GF) γ x) $$ []
    · imodintro; iintro %x %h; cases h
    imod view_input h_vu h_lo msk h_quiet h_mask γ j v (.recv m) Hmode Hb1 trivial hI
        (fun m' h => by cases h; exact Hd) (fun x h => by cases h)
        $$ [Hv Hl] with ⟨%net₀, %xnet₀, Hv, Hl, #Hlb, #Hxlb, %Hmem⟩
    · iframe Hinv Hsw Hsx Hv Hl
    ihave Hco := causeOwn_recv γ j v cause_ptr g Hnf hs hfw Hd Hcnn $$ [cause Hrm Hr1 Hr2]
    · iframe cause Hg Hsent Hrm Hr1 Hr2
    obtain ⟨hR, hip'⟩ : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j
        (v.noteInput (.recv m)) r' ∧ ip' = lcpLen v.r.p.log r'.p.log := by
      rcases Hend γ.R.md rfl with ⟨rfl, rfl⟩ | ⟨hrecv, -, hip⟩
      · exact ⟨AntSim.Reach.stay _ hI (.inr ⟨.recv m, rfl⟩), (lcpLen_self _).symm⟩
      · refine ⟨AntSim.Reach.input _ (.recv m) r' hI rfl rfl rfl
          (fun m' h => by cases h; exact ⟨Hmem.1 m rfl, Hd, (netFacts_recv Hnf hs hfw).1⟩)
          (fun x h => by cases h) ?_, ?_⟩
        · have := hrecv ty0 hty0 (AdmFold γ.dec γ.R.c0)
          rw [hm0] at this
          show RecvEndR _ (γ.R.k j) _ _ _ _
          rw [← hk]; exact this
        · rw [hip]; exact Nat.min_eq_right (lcpLen_le_left _ _)
    ihave Hown := Hclose $$ %_ %r' %ip' %(.recv m) %net₀ %xnet₀ %([] : List XMsg) %cause_ptr Hrnf Hraw
      %(⟨rfl, rfl, rfl, rsView_noteInput (.recv m) hrv rfl rfl rfl rfl rfl rfl, hR, hip', .inr (.inl rfl),
        viewNormal_noteInput hN (fun _ h => by
          cases h; obtain ⟨-, hn, hi, hl, hp⟩ := netFacts_recv Hnf hs hfw; exact ⟨hn, hi, hl, hp⟩)⟩)
      Htb Hcause Hv Hl Hlb Hxlb Hco
    have hin := wp_input c γ n j (v.noteInput (.recv m)) net₀ xnet₀ r' [] q slice.nil
    rw [show (v.noteInput (.recv m)).byE = go!"recv" from rfl] at hin
    rw [show decide (st.msg.Type' = W32 2) = false from decide_eq_false hnp]
    cases err <;>
    · try wp_auto
      wp_apply hin $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby⟩
      · ipureintro; exact Hb1
      icases nodeOwn_drained_reset c γ j n v' $$ Hown with ⟨%cl, Hcause, Hclose'⟩
      try wp_auto
      ihave Hown := Hclose' $$ Hcause
      iapply HΦ
      iframe Hown Had Htok
  · -- a transfer message
    iunfold netXMsg at Hnx
    icases Hnx with ⟨⟨%cm, Hm, %Hcm⟩, %Hxf, Htlb, #Hsent, #Hldr, #Hack⟩
    obtain ⟨hmod, hcs⟩ := Hcm
    obtain ⟨hns, hnp, hnr, hmt⟩ := xnetFacts_types Hxf
    have hto : st.msg.To' = AntSim.nodeId j := by rw [← Hxf.2.2.2.2.1, Hd]
    have Hxf' := Hxf
    obtain ⟨-, -, -, hsrc, -, hterm, -, ⟨is, his⟩, -, -, -, -, hents, -⟩ := Hxf'
    ihave Hpair : ⌜x.ty = .timeoutNow → uint.Z x.term ≤ uint.Z v.dur.term⌝ ∗
        nodeOwn c γ j n v .idle $$ [Hown]
    · by_cases htn : st.msg.Type' = MsgTimeoutNow
      · ihave Hk := Hack $$ %htn
        icases Hk with ⟨%i, %hi, #Hai⟩
        ihave #Hai' : isAcked γ.raft.raftNames (AntSim.nodeId j) st.msg.Term' i $$ []
        · rw [← hto]; iexact Hai
        icases nodeOwn_acked (GF := GF) c γ j n v st.msg.Term' i $$ [Hown] with ⟨%hle, Hown⟩
        · iframe Hown Hai'
        iframe Hown
        ipureintro; intro _; rw [hterm]; exact hle hi
      · iframe Hown
        ipureintro; intro h
        rcases Hxf.2.2.1 with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact absurd h1 htn
        · rw [h2] at h; cases h
    icases Hpair with ⟨%hxt, Hown⟩
    have hrd := msgPtsCC_readE (GF := GF) ml (needsCap st.msg) cm hcs DFrac.discard DFrac.discard
    rw [discard_op_discard, hmod] at hrd
    icases hrd $$ Hm with ⟨Hmh, Hmb⟩
    icases nodeOwn_idle_open h_bp c γ j n v $$ Hown with
      ⟨%rn, %rs, Hrnf, Hraw, Htc, #Hb, %Hst, Hcause, Hv, Hl, %Hpr, Hclose⟩
    obtain ⟨hrv, hI, hP, hN, hk⟩ := Hpr
    icases h_wf γ.R.md hs hcc hfw has _ _ _ _ _ _ _ $$ Hraw with ⟨%Hwf, Hraw⟩
    icases h_tc γ.R.md hs hcc hfw has _ _ _ _ _ _ _ $$ Hraw with ⟨%Htcle, Hraw⟩
    have hnorm : AllNormal st.ents := by rw [hents]; intro e he; cases he
    wp_take_receipt as Hr1
    wp_apply +noauto wp_GetType.1 ml _ _ _ st $$ [$Hpb $Hmh] as Hmh
    rw [Hbatch]
    wp_take_receipt as Hr2
    wp_apply +noauto wp_GetType.1 ml _ _ _ st $$ [$Hpb $Hmh] as Hmh
    wp_take_receipt as Hr3
    wp_apply +noauto wp_msgOf ml _ _ _ st (AntSim.nodeId j) γ.mode.Nodes' hns hnorm
      $$ [$Hpkg $Hmh] as %g ⟨Hmh, #Hg, Hrm⟩
    iclear Hrm
    ihave Hm := Hmb $$ Hmh
    wp_take_receipt as Hr4
    icases typedPointsto_not_null_dup _ _ _ $$ cause with ⟨cause, %Hcnn⟩
    ihave Hrb := receipt_ite (GF := GF) (st.msg.Type' = MsgTimeoutNow) $$ Hr4
    imod h_bstep γ.raft rs.tc st.msg.Term' (st.msg.Type' = MsgTimeoutNow) ⊤ (by solve_ndisj)
      $$ Hb Htc Htlb Hrb with ⟨%Hbd, %tb, Htb, %Hle⟩
    have htt : uint.Z rs.term ≤ uint.Z rs.tc := by rw [← Hwf.2.2]; exact Htcle
    have hle1 : uint.Z rs.tc ≤ uint.Z tb := by split at Hle <;> omega
    have hle2 : uint.Z st.msg.Term' ≤ uint.Z tb := by split at Hle <;> omega
    have htn' : st.msg.Type' = MsgTimeoutNow →
        max (uint.Z ({ rs with tc := tb } : RNState).term) (uint.Z st.msg.Term') + 1 ≤
          uint.Z ({ rs with tc := tb } : RNState).tc := fun h => by
      rw [if_pos h] at Hle; simp only; omega
    ihave Hraw := h_raise γ.R.md hs hcc hfw has _ _ _ _ _ _ _ tb hle1 $$ Hraw
    imod rdCred_of_receipt (GF := GF) γ st $$ Hrdm Hr3 with Hcr
    ihave Hm' : (∃ c : MsgC, msgPtsCC ml (DFrac.own 1) DFrac.discard (needsCap st.msg) c ∗
        ⌜c.model = st ∧ c.csUfNil ∧ (∀ b, γ.raft.raftNames.maxData = some b →
          st.msg.Type' ≠ MsgSnap → msgSizeOk c)⌝) $$ [Hm]
    · iexists cm; iframe Hm; ipureintro
      exact ⟨hmod, hcs, fun b hb => by rw [Hst.2.2] at hb; cases hb⟩
    ihave #Hxfer : □ (⌜st.msg.Type' = MsgTransferLeader ∧ st.msg.Term' ≠ W64 0⌝ -∗
        isLeader γ.raft.raftNames (AntSim.nodeId j) st.msg.Term') $$ []
    · imodintro; iintro %h; rw [← hto]; iapply Hldr; ipureintro; exact h
    ihave #Hmsg : □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
        isMessage γ.raft.raftNames (absMsg ty st.msg st.ents st.ctx)) $$ []
    · imodintro; iintro %ty %hty' %-
      rw [hmt] at hty'; cases hty'
    have hnok : NetMsgOk (AntSim.nodeId j) st := hto ▸ Hxf.2.1
    obtain ⟨hstt, hnhb⟩ := xnetFacts_stepTypes Hxf
    wp_apply +noauto wp_Step γ.R.md hs hcc hfw has γ.raft.raftNames rn (AntSim.nodeId j)
        { rs with tc := tb } v.r [] v.r.p.log.length ml st hnok
        (fun md' hmd => by
          subst hmd
          refine ⟨hstt, fun _ h => absurd h hnhb, fun hnv => ?_, fun _ => ?_⟩
          · rw [Hst.2.1, ← hsrc, his]
            exact nodeId_mem_voters0 Hmode.1 Hmode.2 hnv is
          · -- (antithesis parity B1, transfer source) the sender a server, which raft's names acknowledge
            rw [← hsrc, his]
            exact Hnames.2.2 is)
        hle2 htn' hrv.2.2.2.2.2.1 Hst.1
        $$ [$Hrpkg $Hraw $Hm' $Hxfer $Hmsg Hcr] as %err %t %r' %ip' ⟨Hraw, %Ht, %Hend⟩
    · isplitr
      · imodintro; iintro %h; iexfalso; ipureintro; exact hns h
      · iexact Hcr
    ihave #Hsw : □ (∀ m', ⌜AntSim.Input.recvX x = .recv m'⌝ -∗ sentW (GF := GF) γ m') $$ []
    · imodintro; iintro %m' %h; cases h
    ihave #Hsx : □ (∀ x', ⌜AntSim.Input.recvX x = .recvX x'⌝ -∗ xsentW (GF := GF) γ x') $$ []
    · imodintro; iintro %x' %h; cases h; iexact Hsent
    imod view_input h_vu h_lo msk h_quiet h_mask γ j v (.recvX x) Hmode Hb1 h_tr hI
        (fun m' h => by cases h) (fun x' h => by cases h; exact Hd)
        $$ [Hv Hl] with ⟨%net₀, %xnet₀, Hv, Hl, #Hlb, #Hxlb, %Hmem⟩
    · iframe Hinv Hsw Hsx Hv Hl
    ihave Hco := causeOwn_recvX γ j v cause_ptr g Hxf Hd Hcnn $$ [cause Hr1 Hr2]
    · iframe cause Hg Hsent Hr1 Hr2
    obtain ⟨hR, hip'⟩ : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j
        (v.noteInput (.recvX x)) r' ∧ ip' = lcpLen v.r.p.log r'.p.log := by
      rcases Hend γ.R.md rfl with ⟨rfl, rfl⟩ | ⟨-, hx, hip⟩
      · exact ⟨AntSim.Reach.stay _ hI (.inr ⟨.recvX x, rfl⟩), (lcpLen_self _).symm⟩
      · refine ⟨AntSim.Reach.input _ (.recvX x) r' hI rfl rfl rfl (fun m' h => by cases h)
          (fun x' h => by cases h; exact ⟨Hmem.2 x rfl, Hd, hxt⟩)
          (hx x (xnetFacts_xmsgOf Hxf)), ?_⟩
        rw [hip]; exact Nat.min_eq_right (lcpLen_le_left _ _)
    ihave Hown := Hclose $$ %_ %r' %ip' %(.recvX x) %net₀ %xnet₀ %([] : List XMsg) %cause_ptr Hrnf Hraw
      %(⟨rfl, rfl, rfl, rsView_noteInput (.recvX x) hrv rfl rfl rfl rfl rfl rfl, hR, hip', .inr (.inl rfl),
        viewNormal_noteInput hN (fun _ h => by cases h)⟩)
      Htb Hcause Hv Hl Hlb Hxlb Hco
    have hin := wp_input c γ n j (v.noteInput (.recvX x)) net₀ xnet₀ r' [] q slice.nil
    rw [show (v.noteInput (.recvX x)).byE = go!"recv" from rfl] at hin
    rw [show decide (st.msg.Type' = W32 2) = false from decide_eq_false hnp]
    cases err <;>
    · try wp_auto
      wp_apply hin $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby⟩
      · ipureintro; exact Hb1
      icases nodeOwn_drained_reset c γ j n v' $$ Hown with ⟨%cl, Hcause, Hclose'⟩
      try wp_auto
      ihave Hown := Hclose' $$ Hcause
      iapply HΦ
      iframe Hown Had Htok

end proof

end AntHarness
end EtcdGrove
end Perennial
