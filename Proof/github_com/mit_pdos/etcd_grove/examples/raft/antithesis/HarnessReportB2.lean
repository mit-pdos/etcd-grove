/-
Lean-first (no Rocq counterpart). #33 parity B2: **a report through the run's invariant under B2**
(`HarnessReport`'s `report_upd` over `antClusterB2`): the invariant `antInvB2` (its relation
`AntRunD`, over `AntSimD`), the report's Sim step a B2 statement's (`SimPreD`/`SimStepD`), and the
run's over arm ruled out by a share of the run's liveness (`runLive`, which B2's node goroutines carry
outside their node state) instead of the node's `live` token:
- `runLive_excl`: a share excludes the whole liveness;
- `antRunD_snoc`: the run's pure facts after a report;
- `report_updB2`: `reports γ.strm [ev] Φ` from the report's Sim step, its receipt, the view fragment
  and a liveness share.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReport
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDur

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The run under B2 after a report** `ev` (`antRun_snoc`'s, over `AntSimD`). -/
theorem antRunD_snoc (GF : BundledGFunctors) [ReceiptGS GF] {R : AntSim.RunCfg} {dec : CCDec}
    {evs : List AntCheck.Event} {S S' : AntCheck.State} {V V' : Fin R.N → AntSim.NodeView}
    {net net' : List Msg} {xnet xnet' : List XMsg} {ev : AntCheck.Event}
    (hR : AntRunD R dec evs S V net xnet) (hP' : AntSim.Prefix R.cfg (evs ++ [ev]) S')
    (hA' : AntSim.AntSimD R dec S' V' net' xnet') (hnums : ev.NumsOk) (hchg : ev.ChgOk 0)
    (hfit : Stream.Fits GF (evs ++ [ev])) (hrf : antRunFits GF) :
    AntRunD R dec (evs ++ [ev]) S' V' net' xnet' := by
  obtain ⟨-, -, hB, hCB, hC⟩ := hR
  obtain ⟨E, -, hE⟩ := hCB
  refine ⟨hP', hA', ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · unfold Stream.Fits at hfit
      unfold antRunFits at hrf
      rw [weight_sum'] at hfit
      simp only [List.length_append, List.length_singleton, AntCheck.numBound] at hfit ⊢
      push_cast
      omega
    · intro e he
      rcases List.mem_append.1 he with h | h
      · exact hB.2 e h
      · rw [List.mem_singleton.1 h]; exact hnums
  · refine ⟨0, ?_, ?_⟩
    · intro e he
      rcases List.mem_append.1 he with h | h
      · exact hC e h
      · rw [List.mem_singleton.1 h]; exact hchg
    · have h1 : ((R.cfg.initVoters.length : Nat) : Int) ≤
          ((R.cfg.initVoters.length + (2 + 2 * evs.length + (evs.map AntCheck.Event.size).sum) * E : Nat) : Int) := by
        exact_mod_cast Nat.le_add_right _ _
      simp only [Nat.mul_zero, Nat.add_zero]
      exact Int.lt_of_le_of_lt h1 hE
  · intro e he
    rcases List.mem_append.1 he with h | h
    · exact hC e h
    · rw [List.mem_singleton.1 h]; exact hchg

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

instance nodeROB2_persistent (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N) :
    Persistent (nodeROB2 (GF := GF) c γ n j) := by
  unfold nodeROB2; infer_instance

instance antClusterB2_persistent (c : Loc) (γ : AntNamesB2) :
    Persistent (antClusterB2 (GF := GF) c γ) := by
  constructor
  unfold antClusterB2
  iintro ⟨%cfg, %r, %ns, %stop, #H1, %H2, %H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11, #H12, %H13,
    #H14, #H15, #H16, %H17⟩
  imodintro
  iexists cfg, r, ns, stop
  iframe H1 H4 H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16
  ipureintro; exact ⟨H2, H3, H13, H17⟩

instance antOpenB2_timeless (γ : AntNames) : Timeless (antOpenB2 (GF := GF) γ) := by
  unfold antOpenB2; infer_instance

instance antInvB2_timeless (γ : AntNamesB2) : Timeless (antInvB2 (GF := GF) γ) := by
  unfold antInvB2 runLive; infer_instance

/-- **A share of the run's liveness excludes the whole of it** (the run is not over). -/
theorem runLive_excl (γ : AntNamesB2) (q : Qp) :
    runLive (GF := GF) γ q ∗ runLive γ 1 ⊢ False := by
  unfold runLive
  iintro ⟨H1, H2⟩
  ihave %H := dghostVar_valid_2 γ.liveR () (.own 1) () (.own q) $$ H2 H1
  exfalso
  have := DFrac.valid_own_op H.1
  simp at this

/-- `report_updB2`'s atomic update (`report_au`'s, under B2). -/
theorem report_auB2 (h_vu : view_update.law (GF := GF))
    (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (v v' : AntSim.NodeView)
    (ev : AntCheck.Event) (net₀ add : List Msg) (xnet₀ xadd : List XMsg)
    (Q : AntSim.RaftFacts → AntSim.RaftFacts → Prop) (Φ : IProp GF)
    (hnums : ev.NumsOk) (hchg : ev.ChgOk 0)
    (hstep : ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPreD γ.R γ.dec S V net xnet evs G0 → (∀ i : Fin γ.R.N, (V i).r.full ∈ G0.logs) →
      Q G0 G → V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStepD γ.R γ.dec evs G ev (AntSim.setV V j v') (net ++ add) (xnet ++ xadd) ∧
        AntSim.RaftLaws G ∧ ∀ i : Fin γ.R.N, (AntSim.setV V j v' i).r.full ∈ G.logs) :
    iprop(antClusterB2 (GF := GF) c γ ∗ sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗
        □ factsExt γ.toAntNames Q) ∗
        iprop(viewFrag γ.toAntNames j v ∗ runLive γ q ∗
          (viewFrag γ.toAntNames j v' ∗ runLive γ q ∗
            (∃ (net : List Msg) (xnet : List XMsg), sentLb γ.toAntNames net ∗ xsentLb γ.toAntNames xnet ∗
              ⌜net₀ <+: net ∧ (∀ m ∈ add, m ∈ net) ∧ xnet₀ <+: xnet ∧ ∀ x ∈ xadd, x ∈ xnet⌝) -∗ Φ)) ⊢
      AU <{ ∃∃ evs, recAuth (GF := GF) γ.strm evs }> @ ⊤, ∅
        <{ recAuth γ.strm (evs ++ [ev]) ∗ ⌜Stream.Fits GF (evs ++ [ev])⌝, COMM Φ }> := by
  refine sep_and.trans (aupd_intro ?_)
  iintro ⟨⟨#Hc, #Hlb, #Hxlb, #Hext⟩, ⟨Hv, Hl, HΦ⟩⟩
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, -, -, -, -, -, -, #Hinv, %Hrf, -⟩
  iunfold sentLb at Hlb
  iunfold xsentLb at Hxlb
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold antInvB2 at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpenB2 at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G0, Hstr, Hviews, Hnet, Hxnet, %Hpure, #HF0⟩
    iunfold factsExt at Hext
    imod Hext $$ %G0 %Hpure.2.1 HF0 with ⟨%G, #HF, %HQ⟩
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    ihave %Hxpre := mono_list_auth_lb_valid (GF := GF) γ.xsent 1 xnet xnet₀ $$ Hxnet Hxlb
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists ⟨evs, ⟨⟩⟩
    simp only [Std.Tele.app]
    unfold recAuth
    iframe Hstr
    isplit
    · iintro Hstr
      imod Hmask with -
      imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
      · inext
        iunfold antInvB2
        ileft
        iunfold antOpenB2
        iexists evs, S, V, net, xnet, G0
        iframe Hstr Hviews Hnet Hxnet HF0
        ipureintro; exact Hpure
      imodintro
      iframe Hv Hl HΦ
    · iintro %y ⟨Hstr, %Hfit⟩
      imod Hmask with -
      imod h_vu (⊤ \ ↑antN) γ.toAntNames j V v v' $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
      · iframe Hv Hviews
      obtain ⟨hR, hL0, hG0, hlogs0⟩ := Hpure
      obtain ⟨⟨S', hP', hA', hG'⟩, hL, hlogs⟩ :=
        hstep evs S V net xnet G0 G ⟨hR.1, hR.2.1, hL0, hG0⟩ hlogs0 HQ HVj Hpre.2 Hxpre.2
      have hR' := antRunD_snoc GF hR hP' hA' hnums hchg Hfit Hrf
      imod monoListAuthOwn_update_app (GF := GF) (γ := γ.sent) add $$ Hnet with ⟨Hnet, #Hlb'⟩
      imod monoListAuthOwn_update_app (GF := GF) (γ := γ.xsent) xadd $$ Hxnet with ⟨Hxnet, #Hxlb'⟩
      imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
      · inext
        iunfold antInvB2
        ileft
        iunfold antOpenB2
        iexists evs ++ [ev], S', AntSim.setV V j v', net ++ add, xnet ++ xadd, G
        iframe Hstr Hviews Hnet Hxnet HF
        ipureintro; exact ⟨hR', hL, hG', hlogs⟩
      imodintro
      iapply HΦ
      iframe Hv Hl
      iexists net ++ add, xnet ++ xadd
      iunfold sentLb
      iunfold xsentLb
      iframe Hlb' Hxlb'
      ipureintro
      exact ⟨Hpre.2.trans (List.prefix_append _ _), fun m hm => List.mem_append_right _ hm,
        Hxpre.2.trans (List.prefix_append _ _), fun x hx => List.mem_append_right _ hx⟩
  · iexfalso
    iapply runLive_excl γ q
    iframe Hl Hover

/-- **A report's update under B2** (`report_upd`'s): with the report's B2 Sim step `hstep` (a
`StmtsB2` statement at the invariant's state), its numbers and names unchanged, its receipt, node
`j`'s view fragment and a share `q` of the run's liveness, `reports γ.strm [ev] Φ`: at the commit the
view is `v'`, the messages `add`, `xadd` sent, and the caller gets new lower bounds of the sent
lists. -/
theorem report_updB2 (h_vu : view_update.law (GF := GF))
    (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (v v' : AntSim.NodeView)
    (ev : AntCheck.Event) (net₀ add : List Msg) (xnet₀ xadd : List XMsg)
    (Q : AntSim.RaftFacts → AntSim.RaftFacts → Prop) (Φ : IProp GF)
    (hnums : ev.NumsOk) (hchg : ev.ChgOk 0)
    (hstep : ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPreD γ.R γ.dec S V net xnet evs G0 → (∀ i : Fin γ.R.N, (V i).r.full ∈ G0.logs) →
      Q G0 G → V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStepD γ.R γ.dec evs G ev (AntSim.setV V j v') (net ++ add) (xnet ++ xadd) ∧
        AntSim.RaftLaws G ∧ ∀ i : Fin γ.R.N, (AntSim.setV V j v' i).r.full ∈ G.logs) :
    antClusterB2 (GF := GF) c γ ∗ sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗
        □ factsExt γ.toAntNames Q ∗ ⧗ ev.weight ∗ viewFrag γ.toAntNames j v ∗ runLive γ q ∗
        (viewFrag γ.toAntNames j v' ∗ runLive γ q ∗
          (∃ (net : List Msg) (xnet : List XMsg), sentLb γ.toAntNames net ∗ xsentLb γ.toAntNames xnet ∗
            ⌜net₀ <+: net ∧ (∀ m ∈ add, m ∈ net) ∧ xnet₀ <+: xnet ∧ ∀ x ∈ xadd, x ∈ xnet⌝) -∗ Φ) ⊢
      reports γ.strm [ev] Φ := by
  simp only [reports]
  iintro ⟨#Hc, #Hlb, #Hxlb, #Hext, Hr, Hv, Hl, HΦ⟩
  iframe Hr
  iapply report_auB2 h_vu c γ j q v v' ev net₀ add xnet₀ xadd Q Φ hnums hchg hstep
  iframe Hc Hlb Hxlb Hext Hv Hl HΦ

end proof

end AntHarness
end EtcdGrove
end Perennial
