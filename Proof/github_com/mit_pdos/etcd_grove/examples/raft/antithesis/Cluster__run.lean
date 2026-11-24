/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__run.lean`: the ticker made
(`time.NewTicker`, the configuration's tick positive), a loop whose invariant is node `j` between
inputs (`nodeOwn … .idle`), over a `select` of three cases:
- the stop channel closed (a broadcast): the ticker stopped, `nodesWg.Done()` with the right to
  report and the network adders' share (`nodeExit`), return;
- a tick: the term ceiling raised by a receipt (`rnBudget_spend`), `RawNode.Tick` (`TickEnd`), the
  view noted (`view_input`), the drain from its loop head (`Reach.input`);
- an input (`n.in`'s bag: `inputOk`): a message's report made (`msgOf` on half of it, two more
  receipts from the calls' resolutions), the cell set, the ceiling raised to the message's term
  (`rnBudget_step`), `RawNode.Step` (`RecvEnd`), the view noted, the drain, the cell reset; a
  proposal's `RawNode.Propose` (`ProposeEnd`), the view noted, the drain.

The drain's post says the view's `by` is kept, which a tick's or a proposal's drain needs: the
cause cell stays `nil`, the Go does not reset it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__drain
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.msgOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRunLaws
public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.Ticker__Stop
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Cluster.run.wp_proof
    (wp_NewTicker : time.NewTicker.spec (GF := GF) (hG := hG))
    (wp_TStop : time.Ticker.Stop.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (wp_msgOf : msgOf.spec (GF := GF) (hG := hG))
    (wp_drain : Cluster.drain.spec (GF := GF) (hG := hG))
    (wp_Tick : RawNode.Tick.apiSpec (GF := GF) (hG := hG))
    (wp_Step : RawNode.Step.apiSpec (GF := GF) (hG := hG))
    (wp_Propose : RawNode.Propose.apiSpec (GF := GF) (hG := hG))
    (h_wf : rawNode_wf.law (GF := GF) (hG := hG))
    (h_tc : rawNode_term_tc.law (GF := GF) (hG := hG))
    (h_raise : rawNode_raise_tc.law (GF := GF) (hG := hG))
    (h_bp : rnBudget_persistent.law (GF := GF) (hG := hG))
    (h_spend : rnBudget_spend.law (GF := GF) (hG := hG))
    (h_step : rnBudget_step.law (GF := GF) (hG := hG)) :
    Cluster.run.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v q
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok, Hdone⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, #Hr, #Hrec, #Hro, %Hlen, #Hn0, #Hn1, #Hn2,
    #Hstop, #Hbc, #Hnj, #Hinv, %Hfits⟩
  ihave #Hn' := Hn
  iunfold nodeRO at Hn'
  icases Hn' with ⟨%ch, #Hid, #Hname, #Hin, #Hbag⟩
  ihave #Hsch := ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
  ihave #Htpkg : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave Hcf := Hcfg
  iStructNamed Hcf
  wp_auto
  wp_apply wp_NewTicker as %t %tch %γt #Ht
  · ipureintro; exact Hcok.2.1
  ihave #Ht' := Ht
  iunfold time.isTicker at Ht'
  icases Ht' with ⟨#HtC, #HtI, #HtR, #Htbag⟩
  (try wp_auto)
  ihave IH : iprop(∃ v : AntSim.NodeView, nodeOwn c γ j n v .idle ∗ netAdder c γ q ∗ threadTok ∗
      sync.join.ownDone (c.[H.Cluster, go!"nodesWg"]) (nodeExit c γ j q)) $$ [Hown Had Htok Hdone]
  · iexists v; iframe Hown Had Htok Hdone
  wp_for_core
  icases IH with ⟨%v, Hown, Had, Htok, Hdone⟩
  wp_auto_lc 1
  irename Hlc1 => Hlc0
  cleanup_bool_decide
  wp_auto_lc 1
  irename Hlc0 => Hlc2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the run stops
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stop, γ.stopCh
    isplit
    · ipureintro; rfl
    isplit
    · iexact Hsch
    iapply broadcast_chan_receive $$ Hbc
    iintro -
    (try wp_auto)
    wp_apply wp_TStop t $$ []
    · iexists tch, γt; iexact Ht
    (try wp_auto)
    icases nodeOwn_idle_open h_bp c γ j n v $$ Hown with ⟨%rn, %rs, -, -, -, -, -, -, -, Hl, -, -⟩
    wp_apply (sync.join.WaitGroup.wp_Done_of wp_Done (nodeExit c γ j q) _) $$ [$Hsync $Hdone Hl Had]
    · iunfold nodeExit; iframe Hl Had
    (try wp_auto)
    wp_for_post
    iapply HΦ; iexact Htok
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a tick
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
    inext
    iintro %tm0 -
    icases nodeOwn_idle_open h_bp c γ j n v $$ Hown with
      ⟨%rn, %rs, #Hrn, Hraw, Htc, #Hb, %Hstat, Hcause, Hv, Hl, %Hst, Hclose⟩
    obtain ⟨hrv, hI, hP, hN⟩ := Hst
    icases h_wf _ _ _ _ _ _ _ $$ Hraw with ⟨%Hwf, Hraw⟩
    icases h_tc _ _ _ _ _ _ _ $$ Hraw with ⟨%Htcle, Hraw⟩
    wp_take_receipt as Hrc
    imod h_spend γ.raft rs.tc ⊤ (by solve_ndisj) $$ Hb Hrc Htc with ⟨%Hbd, Htc⟩
    ihave Hraw := h_raise _ _ _ _ _ _ _ (rs.tc + W64 1) (by word) $$ Hraw
    wp_apply wp_Tick γ.raft.raftNames rn (AntSim.nodeId j) { rs with tc := rs.tc + W64 1 } v.ps []
        v.ps.log.length (by simp only; rw [← Hwf.2.2]; word) hrv.2.2.2.2.2.2
        (fun h => absurd Hstat.1 h) $$ [$Hrpkg $Hraw] as %tt %ps' %ip' ⟨Hraw, %Ht, %Hend⟩
    obtain ⟨hTE, hip⟩ := Hend trivial Hstat.1
    ihave #Hsw : □ (∀ m, ⌜AntSim.Input.tick = .recv m⌝ -∗ sentW (GF := GF) γ m) $$ []
    · imodintro; iintro %m %h; cases h
    imod view_input γ j v .tick hI (fun m h => by cases h) $$ [Hv Hl] with
      ⟨%net₀, Hv, Hl, #Hlb, -⟩
    · iframe Hinv Hsw Hv Hl
    ihave Hco := causeOwn_noRecv (GF := GF) γ j v .tick byE_tick_ne
    have hR : AntSim.Reach (AntSim.nodeId j) net₀ (v.noteInput .tick) ps' :=
      AntSim.Reach.input _ .tick ps' hI rfl rfl (fun m h => by cases h)
        (by rw [rnCfg_cfgM3 Hstat.2.1] at hTE; exact hTE)
    have hip' : ip' = lcpLen v.ps.log ps'.log := by
      rw [hip]; exact Nat.min_eq_right (lcpLen_le_left _ _)
    ihave Hown := Hclose $$ %_ %ps' %ip' %(v.noteInput .tick) %net₀ %null Hraw
      %(⟨rfl, rfl, rsView_input hrv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl, hR, hip', .inr (.inr (.inl rfl)),
        viewNormal_noteInput hN (fun _ h => by cases h)⟩)
      Htc Hcause Hv Hl Hlb Hco
    have hdr := wp_drain c γ n j (v.noteInput .tick) net₀ ps' q
    rw [show (v.noteInput .tick).byE = go!"tick" from rfl] at hdr
    wp_apply hdr $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby⟩
    ihave Hown := nodeOwn_drained_idle c γ j n v' (by rw [Hby]; exact byE_tick_ne) $$ Hown
    wp_for_post
    unfold named
    iframe
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- an input
    simp only [chan.blockingClausePre]
    iexists H.input, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ.inCh j
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %inp Hinp
    icases nodeOwn_idle_open h_bp c γ j n v $$ Hown with
      ⟨%rn, %rs, #Hrn, Hraw, Htc, #Hb, %Hstat, Hcause, Hv, Hl, %Hst, Hclose⟩
    obtain ⟨hrv, hI, hP, hN⟩ := Hst
    iunfold inputOk at Hinp
    icases Hinp with (⟨%Hk, %st, %m, Hnm, %Hd⟩ | ⟨%Hk, %data, #Hdata, Hprop⟩)
    · -- a message
      (try wp_auto)
      wp_if_destruct
      · iunfold netMsg at Hnm
        icases Hnm with ⟨⟨%cm, Hm, %Hcm⟩, %Hnf, #Hism, Htlb, #Hsent⟩
        obtain ⟨hmod, hcs⟩ := Hcm
        have hrd := msgPtsCC_readE (GF := GF) inp.msg' (needsCap st.msg) cm hcs DFrac.discard
          DFrac.discard
        rw [discard_op_discard] at hrd
        icases hrd $$ Hm with ⟨Hmh, Hmb⟩
        rw [hmod]
        have hty := Hnf.2.1
        wp_apply +noauto wp_msgOf inp.msg' _ DFrac.discard false st (AntSim.nodeId j)
          (antStepTypes_ne_snap hty) Hnf.2.2.2.1 $$ [$Hpkg $Hmh] as %g ⟨Hmh, #Hg, Hrm⟩
        ihave Hm := Hmb $$ Hmh
        wp_take_receipt as Hr1
        imod receipt_zero (GF := GF) with Hr0
        have hs := h_step γ.raft rs.tc st.msg.Term' False ⊤ (by solve_ndisj)
        simp only [ite_false, Int.add_zero] at hs
        imod hs $$ Hb Htc Htlb Hr0 with ⟨%Hbd, %tb, Htb, %Hle⟩
        have hle1 : uint.Z rs.tc ≤ uint.Z tb := by omega
        have hle2 : uint.Z st.msg.Term' ≤ uint.Z tb := by omega
        ihave Hraw := h_raise _ _ _ _ _ _ _ tb hle1 $$ Hraw
        imod rdCred_zero_upd (GF := GF) γ.raft.raftNames with Hcr
        have hto : st.msg.To' = AntSim.nodeId j := by rw [← absMsgOf_dst Hnf.2.2.2.2.1, Hd]
        have hnok : NetMsgOk (AntSim.nodeId j) st := hto ▸ Hnf.1
        obtain ⟨ty0, hty0, hns0, hm0, huniq⟩ := netFacts_absMsg Hnf
        ihave Hm' : (∃ c : MsgC, msgPtsCC inp.msg' (DFrac.own 1) DFrac.discard (needsCap st.msg) c ∗
            ⌜c.model = st ∧ c.csUfNil ∧ (∀ b, γ.raft.raftNames.maxData = some b →
              st.msg.Type' ≠ MsgSnap → msgSizeOk c)⌝) $$ [Hm]
        · iexists cm; iframe Hm; ipureintro
          exact ⟨hmod, hcs, fun b hb => by rw [Hstat.2.2] at hb; cases hb⟩
        ihave #Hxfer : □ (⌜st.msg.Type' = MsgTransferLeader ∧ st.msg.Term' ≠ W64 0⌝ -∗
            isLeader γ.raft.raftNames (AntSim.nodeId j) st.msg.Term') $$ []
        · imodintro; iintro %h; iexfalso; ipureintro; exact antStepTypes_ne_transfer hty h.1
        ihave #Hmsg : □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
            isMessage γ.raft.raftNames (absMsg ty st.msg st.ents st.ctx)) $$ []
        · imodintro; iintro %ty %hty' %-
          rw [huniq ty hty', hm0]; iexact Hism
        wp_apply +noauto wp_Step γ.raft.raftNames rn (AntSim.nodeId j) { rs with tc := tb } v.ps []
            v.ps.log.length inp.msg' st hnok (fun _ => ⟨hty, fun h => Hnf.2.2.1 (.inr h), by rw [Hstat.2.1]; exact netFacts_from Hnf⟩) hle2
            (fun h => absurd h (antStepTypes_ne_timeoutNow hty)) hrv.2.2.2.2.2.2 Hstat.1
            $$ [$Hrpkg $Hraw $Hm' $Hxfer $Hmsg Hcr] as %err %tt %ps' %ip' ⟨Hraw, %Ht, %Hend⟩
        · isplitr
          · imodintro; iintro %h; iexfalso; ipureintro; exact antStepTypes_ne_snap hty h
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (antStepTypes_ne_readIndex hty))]; iexact Hcr
        wp_take_receipt as Hr2
        obtain ⟨hRE, hip⟩ := Hend trivial
        have hRE' : RecvEnd AntSim.cfgM3 (AntSim.nodeId j) v.ps m ps' := by
          have := hRE ty0 hty0; rw [hm0, rnCfg_cfgM3 Hstat.2.1] at this; exact this
        ihave #Hsw : □ (∀ m', ⌜AntSim.Input.recv m = .recv m'⌝ -∗ sentW (GF := GF) γ m') $$ []
        · imodintro; iintro %m' %h; cases h; iexact Hsent
        imod view_input γ j v (.recv m) hI (fun m' h => by cases h; exact Hd) $$ [Hv Hl] with
          ⟨%net₀, Hv, Hl, #Hlb, %Hmem⟩
        · iframe Hinv Hsw Hv Hl
        ihave Hco := causeOwn_recv γ j v cause_ptr g Hnf Hd $$ [cause Hg Hsent Hrm Hr1 Hr2]
        · iframe cause Hg Hsent Hrm Hr1 Hr2
        have hR : AntSim.Reach (AntSim.nodeId j) net₀ (v.noteInput (.recv m)) ps' :=
          AntSim.Reach.input _ (.recv m) ps' hI rfl rfl
            (fun m' h => by cases h; exact ⟨Hmem m rfl, Hd, netFacts_term Hnf⟩) hRE'
        have hip' : ip' = lcpLen v.ps.log ps'.log := by
          rw [hip]; exact Nat.min_eq_right (lcpLen_le_left _ _)
        ihave Hown := Hclose $$ %_ %ps' %ip' %(v.noteInput (.recv m)) %net₀ %cause_ptr Hraw
          %(⟨rfl, rfl, rsView_input hrv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl, hR, hip', .inr (.inl rfl),
            viewNormal_noteInput hN (fun _ h => by cases h; exact ⟨netFacts_normal Hnf, netFacts_hbCtx Hnf, netFacts_inNums Hnf, netFacts_notProp Hnf⟩)⟩)
          Htb Hcause Hv Hl Hlb Hco
        have hdr := wp_drain c γ n j (v.noteInput (.recv m)) net₀ ps' q
        rw [show (v.noteInput (.recv m)).byE = go!"recv" from rfl] at hdr
        wp_apply +noauto hdr $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby⟩
        icases nodeOwn_drained_reset c γ j n v' $$ Hown with ⟨%cl, Hcause, Hclose'⟩
        (try wp_auto)
        ihave Hown := Hclose' $$ Hcause
        wp_for_post
        unfold named
        iframe
      · exact absurd Hk Hif
    · -- a proposal
      (try wp_auto)
      wp_if_destruct
      · rw [Hk] at Hif; exact absurd Hif (by decide)
      · iunfold propOk at Hprop
        icases Hprop with ⟨#Hpd, Htk', %Hmd⟩
        wp_apply wp_Propose γ.raft.raftNames rn (AntSim.nodeId j) rs v.ps [] v.ps.log.length
            inp.data' data Hstat.1 $$ [$Hrpkg $Hraw $Hdata $Hpd $Htk'] as %err %ps' %ip'
            ⟨Hraw, Herr, %Hend⟩
        · ipureintro; exact Hmd
        obtain ⟨hPE, hip⟩ := Hend trivial
        rw [absMsg_propose] at hPE
        ihave #Hsw : □ (∀ m, ⌜AntSim.Input.propose data = .recv m⌝ -∗ sentW (GF := GF) γ m) $$ []
        · imodintro; iintro %m %h; cases h
        imod view_input γ j v (.propose data) hI (fun m h => by cases h) $$ [Hv Hl] with
          ⟨%net₀, Hv, Hl, #Hlb, -⟩
        · iframe Hinv Hsw Hv Hl
        ihave Hco := causeOwn_noRecv (GF := GF) γ j v (.propose data) (byE_propose_ne data)
        have hR : AntSim.Reach (AntSim.nodeId j) net₀ (v.noteInput (.propose data)) ps' :=
          AntSim.Reach.input _ (.propose data) ps' hI rfl rfl (fun m h => by cases h) hPE
        have hip' : ip' = lcpLen v.ps.log ps'.log := by
          rw [hip]; exact Nat.min_eq_right (lcpLen_le_left _ _)
        ihave Hown := Hclose $$ %_ %ps' %ip' %(v.noteInput (.propose data)) %net₀ %null Hraw
          %(⟨rfl, rfl, rsView_input hrv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl, hR, hip', .inr (.inr (.inr rfl)),
            viewNormal_noteInput hN (fun _ h => by cases h)⟩)
          Htc Hcause Hv Hl Hlb Hco
        have hdr := wp_drain c γ n j (v.noteInput (.propose data)) net₀ ps' q
        rw [show (v.noteInput (.propose data)).byE = go!"propose" from rfl] at hdr
        wp_apply hdr $$ [$Hpkg $Hc $Hn $Hown $Had $Htok] as %v' ⟨Hown, Had, Htok, %Hby⟩
        ihave Hown := nodeOwn_drained_idle c γ j n v' (by rw [Hby]; exact byE_propose_ne data) $$ Hown
        wp_for_post
        unfold named
        iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end AntHarness
end EtcdGrove
end Perennial
