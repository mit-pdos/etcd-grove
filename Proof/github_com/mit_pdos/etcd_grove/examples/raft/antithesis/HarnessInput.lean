/-
Lean-first (no Rocq counterpart). #33 parity B1: **a node taking an input** (`node.tick`,
`node.campaign`, `node.propose`, `node.step`, `node.unreachable`, ...: the `RawNode` call, then
`input`'s drain), the steps their proofs share, over `HarnessRun.lean`'s `nodeOwn` at `Fin R.N`
(S4's `HarnessRunLaws.lean`, generalized):
- `nodeRaft_open`, `nodeOwn_idle_open`: node `j` between inputs opened into its `RawNode` and the
  rest, with what makes a drain's loop head of it after the input (`nodeOwn … (.loop …)`);
- `view_input`: the view notes the input (`Quiet.input`, `antSim_quiet`), in an update of the run's
  invariant, with lower bounds of the sent lists that have the input's message;
- `causeOwn_noRecv`: the cause cell after an input not a message's (`nil`);
- `nodeOwn_drained_idle`: after a drain not caused by a message, node `j` is between inputs again.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Scope

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `lcpLen` is at most its left list's length. -/
theorem lcpLen_le_left : ∀ (l l' : List EntryM), lcpLen l l' ≤ l.length
  | [], _ => by simp [lcpLen]
  | _ :: _, [] => by simp [lcpLen]
  | a :: l, b :: l' => by
    unfold lcpLen
    split
    · have := lcpLen_le_left l l'; simp only [List.length_cons]; omega
    · simp

/-- Noting an input keeps the view's entries normal, given the input's message's. -/
theorem viewNormal_noteInput {v : AntSim.NodeView} {inp : AntSim.Input} (hN : ViewNormal v)
    (hm : ∀ m, inp.cause = some m → AllNormal m.entries ∧ uint.Z m.index < 2 ^ 61 ∧
      uint.Z m.logterm < 2 ^ 61 ∧ m.ty ≠ .propose) :
    ViewNormal (v.noteInput inp) :=
  ⟨hN.1, fun m h => hm m h⟩

/-- `RsView` reads none of the term, the ceiling, `psnap`, the node constant; nor the view's input
fields (`noteInput`). -/
theorem rsView_noteInput {rs rs' : RNState} {v : AntSim.NodeView} (inp : AntSim.Input)
    (h : RsView rs v)
    (hphs : rs'.phs = rs.phs) (hdur : rs'.dur = rs.dur) (hdel : rs'.delivered = rs.delivered)
    (hsteps : rs'.steps = rs.steps) (hun : rs'.unpersisted = rs.unpersisted) (hflw : rs'.flw = rs.flw) :
    RsView rs' (v.noteInput inp) := by
  unfold RsView at h ⊢
  rw [hphs, hdur, hdel, hsteps, hun, hflw]
  exact h

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-! ## The invariant is timeless -/

instance raftFactsOwn_timeless (γ : RaftNames) (G : AntSim.RaftFacts) :
    Timeless (raftFactsOwn (GF := GF) γ G) := by
  unfold raftFactsOwn; infer_instance

instance antOpen_timeless (γ : AntNames) : Timeless (antOpen (GF := GF) γ) := by
  unfold antOpen; infer_instance

instance antInv_timeless (γ : AntNames) : Timeless (antInv (GF := GF) γ) := by
  unfold antInv nodeLive; infer_instance

/-- **Node `j`'s raft ghost state, opened**: the ceiling's bound, the budget (persistent, by its
law), the cluster's static facts, and what closes it at a record of the same durable state and a
ceiling bounded. -/
theorem nodeRaft_open (hbp : rnBudget_persistent.law (GF := GF)) (γ : AntNames) (j : Fin γ.R.N)
    (rs : RNState) :
    nodeRaft (GF := GF) γ j rs ⊢
      rnTermLB γ.raft rs.tc ∗ □ rnBudget γ.raft ∗
      ⌜γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = γ.R.voters0 ∧
        γ.raft.raftNames.maxData = none⌝ ∗
      (∀ rs' : RNState, ⌜rs'.dur = rs.dur⌝ -∗ rnTermLB γ.raft rs'.tc -∗ nodeRaft γ j rs') := by
  haveI := hbp γ.raft
  unfold nodeRaft
  iintro ⟨%x, %g, Hgv, Hsf, Hdg, Htc, #Hb, %Hst⟩
  iframe Htc
  isplitr
  · iexact Hb
  isplitr
  · ipureintro; exact ⟨Hst.1, Hst.2.1, Hst.2.2.1⟩
  iintro %rs' %hd Htc'
  iexists x, g
  rw [hd]
  iframe Hgv Hsf Hdg Htc' Hb
  ipureintro; exact Hst

/-- **Node `j` between inputs, opened** (a node taking an input): its `RawNode` field and the
`RawNode` at the view's state, nothing queued, the in-progress boundary at the log's end; its raft
ghost state opened (`nodeRaft_open`); the cause cell `nil`, the view fragment and the right to
report; and what makes a drain's loop head of it after the input `inp` (the `RawNode` at the input's
end, reached from the noted view). -/
theorem nodeOwn_idle_open (hbp : rnBudget_persistent.law (GF := GF)) (c : Loc) (γ : AntNames)
    (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) :
    nodeOwn (GF := GF) c γ j n v .idle ⊢
      ∃ (rn : Loc) (rs : RNState),
        n.[H.node, go!"rn"] ↦ rn ∗
        rawNode γ.raft.raftNames {} rn (AntSim.nodeId j) rs v.r [] v.r.p.log.length ∗
        rnTermLB γ.raft rs.tc ∗ □ rnBudget γ.raft ∗
        ⌜γ.raft.raftNames.reTrace = none ∧ γ.raft.raftNames.reCfg = γ.R.voters0 ∧
          γ.raft.raftNames.maxData = none⌝ ∗
        n.[H.node, go!"cause"] ↦ (null : Loc) ∗ viewFrag γ j v ∗ nodeLive γ j ∗
        ⌜RsView rs v ∧ v.Idle ∧ PIdle rs v.r.p ∧ ViewNormal v ∧ rs.k = γ.R.k j⌝ ∗
        (∀ (rs' : RNState) (r₁ : RState) (ip' : Nat) (inp : AntSim.Input) (net₀ : List Msg)
            (xnet₀ : List XMsg) (xs₁ : List XMsg) (cl : Loc),
          n.[H.node, go!"rn"] ↦ rn -∗
          rawNode γ.raft.raftNames {} rn (AntSim.nodeId j) rs' r₁ [] ip' -∗
          ⌜rs'.storage = rs.storage ∧ rs'.dur = rs.dur ∧ rs'.k = rs.k ∧ RsView rs' (v.noteInput inp) ∧
            AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j (v.noteInput inp) r₁ ∧
            ip' = lcpLen v.r.p.log r₁.p.log ∧ ByOk inp.byE ∧ ViewNormal (v.noteInput inp)⌝ -∗
          rnTermLB γ.raft rs'.tc -∗
          n.[H.node, go!"cause"] ↦ cl -∗ viewFrag γ j (v.noteInput inp) -∗ nodeLive γ j -∗
          sentLb γ net₀ -∗ xsentLb γ xnet₀ -∗ causeOwn γ j (v.noteInput inp) cl -∗
          nodeOwn c γ j n (v.noteInput inp) (.loop net₀ xnet₀ r₁ xs₁)) := by
  unfold nodeOwn
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, #Hd, Hmem, Hrn, Hms, Hrole, Hhs, Hcause,
    Happ, Hconf, Hv, Hl, %HN, Hdisk, %si, %rs, %qs, %ip, %r, Hstor, %Hsto, Hraw, Hnr, %Hrv, #Hhsro,
    #Hcs, %Hc0, %Hph⟩
  obtain ⟨hI, rfl, rfl, rfl, hP, rfl⟩ := Hph
  icases nodeRaft_open hbp γ j rs $$ Hnr with ⟨Htc, #Hb, %Hst, Hnrc⟩
  iexists rn, rs
  iframe Hrn Hraw Htc Hcause Hv Hl
  isplitr
  · iexact Hb
  isplitr
  · ipureintro; exact Hst
  isplitr
  · ipureintro; exact ⟨Hrv.1, hI, hP, HN, Hrv.2.2.2.2⟩
  iintro %rs' %r₁ %ip' %inp %net₀ %xnet₀ %xs₁ %cl' Hrn Hraw %Hf Htc Hcause Hv Hl Hlb Hxlb Hco
  obtain ⟨hsto, hdur, hk, hrv, hR, hip, hby, hN'⟩ := Hf
  ihave Hnr := Hnrc $$ %rs' %hdur Htc
  iexists d, rn, ms, hsl, cl', csl, role, applied
  iframe Hd Hmem Hrn Hms Hrole Hhs Hcause Happ Hconf Hv Hl
  isplitr
  · ipureintro; exact hN'
  dsimp only
  rw [show (v.noteInput inp).dur = v.dur from rfl]
  iframe Hdisk
  iexists si, rs', [], ip', r₁
  iframe Hstor Hraw Hnr Hhsro Hcs Hlb Hxlb Hco
  ipureintro
  exact ⟨by rw [hsto]; exact Hsto, ⟨hrv, Hrv.2.1, Hrv.2.2.1, Hrv.2.2.2.1, by rw [hk]; exact Hrv.2.2.2.2⟩,
    Hc0, rfl, hR, rfl, hip, hby⟩

/-- **After a drain not caused by a message**, the cause cell is `nil` (`causeOwn`): node `j` is
between inputs again. -/
theorem nodeOwn_drained_idle (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (h : v.byE ≠ go!"recv") :
    nodeOwn (GF := GF) c γ j n v .drained ⊢ nodeOwn c γ j n v .idle := by
  have hco : ∀ cl, causeOwn (GF := GF) γ j v cl = pendingCause cl none := by
    intro cl; unfold causeOwn; simp only [h, false_and, ↓reduceIte]
  unfold nodeOwn
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, #Hd, Hmem, Hrn, Hms, Hrole, Hhs, Hcause,
    Happ, Hconf, Hv, Hl, %HN, Hdisk, %si, %rs, %qs, %ip, %r, Hstor, %Hsto, Hraw, Hnr, %Hrv, #Hhsro,
    #Hcs, %Hc0, %Hph, Hco⟩
  rw [hco]
  iunfold pendingCause at Hco
  icases Hco with (%Hnil | ⟨%g, %m, %Hc, -⟩)
  · iexists d, rn, ms, hsl, cl, csl, role, applied
    iframe Hd Hmem Hrn Hms Hrole Hhs Hcause Happ Hconf Hv Hl
    isplitr
    · ipureintro; exact HN
    dsimp only
    iframe Hdisk
    iexists si, rs, qs, ip, r
    iframe Hstor Hraw Hnr Hhsro Hcs
    ipureintro
    exact ⟨Hsto, Hrv, Hc0, Hph.1, Hph.2.1, Hph.2.2.1, Hph.2.2.2.1, Hph.2.2.2.2, Hnil.1⟩
  · exfalso; exact absurd Hc.2 (by simp)

/-- **The cause cell after an input not a message's**: `nil`. -/
theorem causeOwn_noRecv (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (inp : AntSim.Input)
    (h : inp.byE ≠ go!"recv") :
    ⊢ causeOwn (GF := GF) γ j (v.noteInput inp) null := by
  unfold causeOwn
  simp only [AntSim.NodeView.noteInput, h, false_and, ↓reduceIte]
  iunfold pendingCause
  ileft
  ipureintro; exact ⟨rfl, rfl⟩

/-! ## The input noted in the view -/

/-- **`antSim_quiet` at the mask `msk`** (`AntSim.antSim_quiet_in`'s statement, below its bound
`msk ≤ mskS4`: the Link passes `antSim_quiet_in msk hmsk`; widened to `mskB1` with the Sim). -/
abbrev antSim_quiet_in.law (msk : AntSim.SimMask) : Prop :=
  ∀ (R : AntSim.RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
    (net : List Msg) (xnet : List XMsg) (G : AntSim.RaftFacts) (n : Fin R.N) (v' : AntSim.NodeView),
    AntSim.InMask msk R net xnet → AntSim.AntSim R dec S V net xnet → AntSim.RaftLaws G →
    AntSim.GlobalOk R S net G → AntSim.QuietIn msk R dec (AntSim.admOf G) net xnet n (V n) v' →
    AntSim.AntSim R dec S (AntSim.setV V n v') net xnet

/-- **A run of the driver is within the mask `msk`** (`AntSim.InMask`), from the cluster's facts
(`InScope`, `ModeRun`), B1's off bits (`DrainB1`) and the run's relation (`AntRun`: every message
sent under the run's mask). Proved for the mask the Link instantiates. -/
abbrev runInMask.law (msk : AntSim.SimMask) : Prop :=
  ∀ (γ : AntNames) (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView)
    (net : List Msg) (xnet : List XMsg),
    InScope γ.scope γ.mode → ModeRun γ.scope γ.mode γ.R → DrainB1 γ.scope γ.mode →
    AntRun γ.R γ.dec evs S V net xnet → AntSim.InMask msk γ.R net xnet

/-- **The view notes an input** (`Quiet.input`, `antSim_quiet`): node `j`'s view between inputs, the
input's message (if any) sent to it; the run's invariant is opened in an update (no step: it is
timeless), its view halves moved to `v.noteInput inp` (`view_update`), the relation re-proved
(`antSim_quiet_in` at a mask `msk` admitting the run, `runInMask`, and the input), and
lower bounds of the sent lists taken, which have the input's message. While node `j` holds its
`live` token the run is not over (`nodeLive_over`). -/
theorem view_input (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (msk : AntSim.SimMask) (h_quiet : antSim_quiet_in.law msk) (h_mask : runInMask.law msk)
    (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (inp : AntSim.Input)
    (hrun : InScope γ.scope γ.mode ∧ ModeRun γ.scope γ.mode γ.R) (hb1 : DrainB1 γ.scope γ.mode)
    (hinp : inp.InMask msk) (hI : v.Idle) (hd : ∀ m, inp = .recv m → m.dst = AntSim.nodeId j)
    (hdx : ∀ x, inp = .recvX x → x.dst = AntSim.nodeId j) :
    inv antN (antInv (GF := GF) γ) ∗ □ (∀ m, ⌜inp = .recv m⌝ -∗ sentW γ m) ∗
        □ (∀ x, ⌜inp = .recvX x⌝ -∗ xsentW γ x) ∗ viewFrag γ j v ∗ nodeLive γ j ⊢
      |={⊤}=> ∃ (net₀ : List Msg) (xnet₀ : List XMsg), viewFrag γ j (v.noteInput inp) ∗
        nodeLive γ j ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗
        ⌜(∀ m, inp = .recv m → m ∈ net₀) ∧ (∀ x, inp = .recvX x → x ∈ xnet₀)⌝ := by
  iintro ⟨#Hinv, #Hs, #Hsx, Hv, Hl⟩
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G, Hstr, Hviews, Hnet, Hxnet, %Hpure, #HF⟩
    ihave %Hmem : ⌜∀ m, inp = .recv m → m ∈ net⌝ $$ [Hnet]
    · by_cases hr : ∃ m, inp = .recv m
      · obtain ⟨m, rfl⟩ := hr
        ihave #Hsm := Hs $$ %m %rfl
        iunfold sentW at Hsm
        icases Hsm with ⟨%i, #Hidx⟩
        ihave %Hlk := mono_list_auth_idx_lookup (GF := GF) γ.sent 1 net i m $$ Hnet Hidx
        ipureintro
        intro m' hm'
        cases hm'
        exact List.mem_of_getElem? Hlk
      · ipureintro; intro m' hm'; exact absurd ⟨m', hm'⟩ hr
    ihave %Hxmem : ⌜∀ x, inp = .recvX x → x ∈ xnet⌝ $$ [Hxnet]
    · by_cases hr : ∃ x, inp = .recvX x
      · obtain ⟨x, rfl⟩ := hr
        ihave #Hsm := Hsx $$ %x %rfl
        iunfold xsentW at Hsm
        icases Hsm with ⟨%i, #Hidx⟩
        ihave %Hlk := mono_list_auth_idx_lookup (GF := GF) γ.xsent 1 xnet i x $$ Hxnet Hidx
        ipureintro
        intro x' hx'
        cases hx'
        exact List.mem_of_getElem? Hlk
      · ipureintro; intro x' hx'; exact absurd ⟨x', hx'⟩ hr
    ihave #Hlb := monoListLbOwn_get (GF := GF) γ.sent 1 net $$ Hnet
    ihave #Hxlb := monoListLbOwn_get (GF := GF) γ.xsent 1 xnet $$ Hxnet
    imod h_vu (⊤ \ ↑antN) γ j V v (v.noteInput inp) $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    obtain ⟨hR, hL, hG, hlogs⟩ := Hpure
    have hin := h_mask γ evs S V net xnet hrun.1 hrun.2 hb1 hR
    obtain ⟨hP, hA, hB, hCB, hC⟩ := hR
    have hq : AntSim.QuietIn msk γ.R γ.dec (AntSim.admOf G) net xnet j (V j) (v.noteInput inp) := by
      rw [HVj]
      exact AntSim.QuietIn.input v inp hinp hI (fun m hm => ⟨Hmem m hm, hd m hm⟩)
        (fun x hx => ⟨Hxmem x hx, hdx x hx⟩)
    have hA' := h_quiet γ.R γ.dec S V net xnet G j (v.noteInput inp) hin hA hL hG hq
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInv
      ileft
      iunfold antOpen
      iexists evs, S, AntSim.setV V j (v.noteInput inp), net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro
      refine ⟨⟨hP, hA', hB, hCB, hC⟩, hL, hG, ?_⟩
      intro i
      unfold AntSim.setV
      split
      · subst_vars; exact hlogs _
      · exact hlogs i
    imodintro
    iexists net, xnet
    iunfold sentLb
    iunfold xsentLb
    iframe Hv Hl Hlb Hxlb
    ipureintro; exact ⟨Hmem, Hxmem⟩
  · iexfalso
    iapply h_lo γ j
    iframe Hl Hover

end laws

end AntHarness
end EtcdGrove
end Perennial
