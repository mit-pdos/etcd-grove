/-
Lean-first (no Rocq counterpart). #33 parity B1: **a report through the run's invariant** (S4's
`DrainReports.report_au`, generalized to `Fin R.N`, the extra-network `xnet` and the Sim's `SimStep`),
shared by every report a node makes (`node.start`'s `boot`, the drain's):

- `factsExt`: raft's facts grown at the invariant's mask (what a report's caller supplies;
  `factsExt_none`: nothing grown);
- `antRun_snoc`: the run's pure facts after a report (the stream's bounds from the receipts' fit);
- `report_upd`: from the report's Sim step (`hstep`, the report's `.stmt`), its receipt, the node's
  view fragment and `live` token, `reports γ.strm [ev] Φ` (`node.emit`'s premise): the invariant
  opened, raft's facts grown, the stream's half given to the recorder; at the commit the report
  appended, the view moved to `v'`, the messages `add`, `xadd` sent.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The run after a report -/

section pure
variable [GooseExts]

theorem weight_sum' (evs : List AntCheck.Event) :
    (evs.map AntCheck.Event.weight).sum = (evs.map AntCheck.Event.size).sum + 2 * evs.length := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, AntCheck.Event.weight, ih]
    omega

/-- **The run after a report** `ev`: the checker took it (`hP'`), the relation holds after it
(`hA'`), and the stream's bounds: the receipts' fit, the report's numbers, no name changed. -/
theorem antRun_snoc (GF : BundledGFunctors) [ReceiptGS GF] {R : AntSim.RunCfg} {dec : CCDec}
    {evs : List AntCheck.Event} {S S' : AntCheck.State} {V V' : Fin R.N → AntSim.NodeView}
    {net net' : List Msg} {xnet xnet' : List XMsg} {ev : AntCheck.Event}
    (hR : AntRun R dec evs S V net xnet) (hP' : AntSim.Prefix R.cfg (evs ++ [ev]) S')
    (hA' : AntSim.AntSim R dec S' V' net' xnet') (hnums : ev.NumsOk) (hchg : ev.ChgOk 0)
    (hfit : Stream.Fits GF (evs ++ [ev])) (hrf : antRunFits GF) :
    AntRun R dec (evs ++ [ev]) S' V' net' xnet' := by
  obtain ⟨-, -, hB, hCB, hC⟩ := hR
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
  · obtain ⟨E, -, hE⟩ := hCB
    refine ⟨0, ?_, ?_⟩
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

/-- **Raft's facts grown, related to the old by `Q`** (persistent; what a report's caller
supplies): any lawful facts `G0`, owned, extend at the invariant's mask to facts `G` with `Q G0 G`.
(`factsExt_none`: `G = G0`.) -/
def factsExt (γ : AntNames) (Q : AntSim.RaftFacts → AntSim.RaftFacts → Prop) : IProp GF :=
  iprop(∀ G0 : AntSim.RaftFacts, ⌜AntSim.RaftLaws G0⌝ -∗ raftFactsOwn γ.raft.raftNames G0 ={⊤ \ ↑antN}=∗
    ∃ G : AntSim.RaftFacts, raftFactsOwn γ.raft.raftNames G ∗ ⌜Q G0 G⌝)

theorem factsExt_none (γ : AntNames) : ⊢ factsExt (GF := GF) γ (fun G0 G => G = G0) := by
  unfold factsExt
  iintro %G0 %_ #HF
  imodintro
  iexists G0
  iframe HF
  ipureintro; rfl

/-- `report_upd`'s atomic update (S4's `report_au`). -/
theorem report_au (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (v v' : AntSim.NodeView)
    (ev : AntCheck.Event) (net₀ add : List Msg) (xnet₀ xadd : List XMsg)
    (Q : AntSim.RaftFacts → AntSim.RaftFacts → Prop) (Φ : IProp GF)
    (hnums : ev.NumsOk) (hchg : ev.ChgOk 0)
    (hstep : ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPre γ.R γ.dec S V net xnet evs G0 → (∀ i : Fin γ.R.N, (V i).r.full ∈ G0.logs) →
      Q G0 G → V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStep γ.R γ.dec evs G ev (AntSim.setV V j v') (net ++ add) (xnet ++ xadd) ∧
        AntSim.RaftLaws G ∧ ∀ i : Fin γ.R.N, (AntSim.setV V j v' i).r.full ∈ G.logs) :
    iprop(antCluster (GF := GF) c γ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ □ factsExt γ Q) ∗
        iprop(viewFrag γ j v ∗ nodeLive γ j ∗
          (viewFrag γ j v' ∗ nodeLive γ j ∗
            (∃ (net : List Msg) (xnet : List XMsg), sentLb γ net ∗ xsentLb γ xnet ∗
              ⌜net₀ <+: net ∧ (∀ m ∈ add, m ∈ net) ∧ xnet₀ <+: xnet ∧ ∀ x ∈ xadd, x ∈ xnet⌝) -∗ Φ)) ⊢
      AU <{ ∃∃ evs, recAuth (GF := GF) γ.strm evs }> @ ⊤, ∅
        <{ recAuth γ.strm (evs ++ [ev]) ∗ ⌜Stream.Fits GF (evs ++ [ev])⌝, COMM Φ }> := by
  refine sep_and.trans (aupd_intro ?_)
  iintro ⟨⟨#Hc, #Hlb, #Hxlb, #Hext⟩, ⟨Hv, Hl, HΦ⟩⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, -, -, -, -, -, -, #Hinv, %Hrf, -⟩
  iunfold sentLb at Hlb
  iunfold xsentLb at Hxlb
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
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
        iunfold antInv
        ileft
        iunfold antOpen
        iexists evs, S, V, net, xnet, G0
        iframe Hstr Hviews Hnet Hxnet HF0
        ipureintro; exact Hpure
      imodintro
      iframe Hv Hl HΦ
    · iintro %y ⟨Hstr, %Hfit⟩
      imod Hmask with -
      imod h_vu (⊤ \ ↑antN) γ j V v v' $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
      · iframe Hv Hviews
      obtain ⟨hR, hL0, hG0, hlogs0⟩ := Hpure
      obtain ⟨⟨S', hP', hA', hG'⟩, hL, hlogs⟩ :=
        hstep evs S V net xnet G0 G ⟨hR.1, hR.2.1, hL0, hG0⟩ hlogs0 HQ HVj Hpre.2 Hxpre.2
      have hR' := antRun_snoc GF hR hP' hA' hnums hchg Hfit Hrf
      imod monoListAuthOwn_update_app (GF := GF) (γ := γ.sent) add $$ Hnet with ⟨Hnet, #Hlb'⟩
      imod monoListAuthOwn_update_app (GF := GF) (γ := γ.xsent) xadd $$ Hxnet with ⟨Hxnet, #Hxlb'⟩
      imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
      · inext
        iunfold antInv
        ileft
        iunfold antOpen
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
    iapply h_lo γ j
    iframe Hl Hover

/-- **A report's update** (every report of a node): with the report's Sim step `hstep` (the
report's `.stmt` at the invariant's state: the view `v` of node `j`, the sent lists past the
caller's lower bounds `net₀`, `xnet₀`, raft's facts `G0` grown to `G` by `Q`), its numbers and its
names unchanged (`hnums`, `hchg`), its receipt, and node `j`'s view fragment and `live` token,
`reports γ.strm [ev] Φ`: at the commit the view is `v'`, the messages `add` and `xadd` are sent, and
the caller gets new lower bounds of the sent lists, which have them. (`node.emit`'s report is
`atNode (nameOf (nodeId j)) e`: the caller instantiates `ev` at it.) -/
theorem report_upd (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (v v' : AntSim.NodeView)
    (ev : AntCheck.Event) (net₀ add : List Msg) (xnet₀ xadd : List XMsg)
    (Q : AntSim.RaftFacts → AntSim.RaftFacts → Prop) (Φ : IProp GF)
    (hnums : ev.NumsOk) (hchg : ev.ChgOk 0)
    (hstep : ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPre γ.R γ.dec S V net xnet evs G0 → (∀ i : Fin γ.R.N, (V i).r.full ∈ G0.logs) →
      Q G0 G → V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStep γ.R γ.dec evs G ev (AntSim.setV V j v') (net ++ add) (xnet ++ xadd) ∧
        AntSim.RaftLaws G ∧ ∀ i : Fin γ.R.N, (AntSim.setV V j v' i).r.full ∈ G.logs) :
    antCluster (GF := GF) c γ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ □ factsExt γ Q ∗ ⧗ ev.weight ∗
        viewFrag γ j v ∗ nodeLive γ j ∗
        (viewFrag γ j v' ∗ nodeLive γ j ∗
          (∃ (net : List Msg) (xnet : List XMsg), sentLb γ net ∗ xsentLb γ xnet ∗
            ⌜net₀ <+: net ∧ (∀ m ∈ add, m ∈ net) ∧ xnet₀ <+: xnet ∧ ∀ x ∈ xadd, x ∈ xnet⌝) -∗ Φ) ⊢
      reports γ.strm [ev] Φ := by
  simp only [reports]
  iintro ⟨#Hc, #Hlb, #Hxlb, #Hext, Hr, Hv, Hl, HΦ⟩
  iframe Hr
  iapply report_au h_vu h_lo c γ j v v' ev net₀ add xnet₀ xadd Q Φ hnums hchg hstep
  iframe Hc Hlb Hxlb Hext Hv Hl HΦ

end proof

end AntHarness
end EtcdGrove
end Perennial
