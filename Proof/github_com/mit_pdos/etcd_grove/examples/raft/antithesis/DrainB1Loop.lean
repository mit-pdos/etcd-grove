/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E (`node.drain`): **the drain's loop
head and its silent steps** (S4's `DrainLoop`, over the parity `nodeOwn`):
- `view_quiet`: a step that reports nothing (`QuietIn`: the loop's exit at `HasReady` false, a
  `Ready` the driver does not report) moves node `j`'s view in the run's invariant (as
  `HarnessInput.view_input` for an input);
- `nodeOwn_loop_open` / `nodeOwn_loop_close`: the `.loop` phase opened to the `RawNode` and the rest;
- `drain_exit`: `HasReady` false at the loop head, the view moved to the node's state
  (`QuietIn.noReady`), the node drained.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The run's mode without B1's off features (HarnessStep's `rMd_flags`, restated here so the drain
does not import node.step's lemmas). -/
theorem rMd_flags_d {s : H.Scope} {m : H.Mode} {R : AntSim.RunCfg} (hmr : ModeRun s m R)
    (hb1 : DrainB1 s m) :
    R.md.snapshots = false ∧ R.md.confChanges = false ∧ R.md.forwarding = false ∧
      R.md.async = false := by
  rw [hmr.2.2.2.2.1]
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4⟩ := hb1
  exact ⟨h1, h2, h3, h4⟩

/-- The Sim's reported role string determines the pre-candidate flag and the protocol role (a
pre-candidate's protocol role a follower). -/
theorem roleStr_inj {p p' : Bool} {r r' : Role} (h : AntSim.roleStr p r = AntSim.roleStr p' r')
    (hp : p = true → r = .follower) (hp' : p' = true → r' = .follower) : p = p' ∧ r = r' := by
  cases p <;> cases p' <;> cases r <;> cases r' <;>
    simp_all [AntSim.roleStr, AntSim.roleOf] <;> revert h <;> decide

/-- **Go's role string of the last reported role, against the view's** (`RsView`'s role clause):
the view's pre-candidate flag is Go's, its protocol role `roleProto`'s. -/
theorem rsView_role {rs : RNState} {v : AntSim.NodeView} (hrv : RsView rs v)
    (hpre : v.pre = true → v.ps.role = .follower) :
    decide (rs.role = StatePreCandidate) = v.pre ∧ roleProto rs.role = v.ps.role := by
  have h := hrv.2.2.2.2.2.2.1
  rw [roleStr_go] at h
  refine roleStr_inj h ?_ hpre
  intro hp
  simp only [decide_eq_true_eq] at hp
  rw [hp]
  simp [roleProto, StatePreCandidate, StateCandidate, StateLeader]

/-- **The loop's exit is quiet** (`QuietIn.noReady`): at a loop head (`Reach` over earlier sent
lists, a driver's `by`) where `HasReady` is false (`PIdle`, no read state), the node's state has the
view's hard state, role and full log (the sync disk), nothing to send or read. -/
theorem quiet_noReady {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {S : AntCheck.State} {V : Fin R.N → AntSim.NodeView} {net₀ net : List Msg}
    {xnet₀ xnet : List XMsg} {j : Fin R.N} {v : AntSim.NodeView} {r₁ : RState} {rs : RNState}
    (hin : AntSim.InMask AntSim.mskB1 R net xnet) (hA : AntSim.AntSim R dec S V net xnet)
    (hVj : V j = v) (hcc : R.md.confChanges = false) (hby : ByOk v.byE)
    (hR : AntSim.Reach R dec Adm net₀ xnet₀ j v r₁) (hn : net₀ <+: net) (hx : xnet₀ <+: xnet)
    (hrv : RsView rs v) (hP : PIdle rs r₁.p) (hrd : r₁.p.rd.states = []) :
    AntSim.QuietIn AntSim.mskB1 R dec Adm net xnet j v { v with r := r₁, qs := [] } ∧
      r₁.full = v.r.full ∧ (r₁.full = v.r.full ∧ r₁.p.role = v.ps.role) := by
  have hri := reachIn_b1 hcc hby hR hn hx
  have hok := hA.2.2.2.2 j
  rw [hVj] at hok
  obtain ⟨hmd, hbt, hpar, hspl, -, -⟩ := hin.b1 mskB1_le
  have hsd := (hok.sync (by rw [hmd]) hbt hspl hpar).2.1
  have hfp := AntSim.reach_fp mskB1_le hin hok hri
  have hfp0 := (hok.facts.snap0 (by rw [hmd])).2.1
  obtain ⟨hob, hphs, hrole, hents⟩ := hP
  have hrv' := hrv
  obtain ⟨hphs', hdents, -, -, -, -, -⟩ := hrv'
  rw [hphs'] at hphs
  simp only [HardStateM.mk.injEq] at hphs
  obtain ⟨ht, hv, hc⟩ := hphs
  have hfull : r₁.full = v.r.full := by
    have : v.dur.log = v.r.full := by rw [hsd]; rfl
    rw [← this, ← hdents, hents, RState.full, hfp, hfp0, List.nil_append]
  have hdt : v.dur.term = v.ps.term ∧ v.dur.vote = v.ps.vote ∧ v.dur.commit = v.ps.commit := by
    rw [hsd]; exact ⟨rfl, rfl, rfl⟩
  have hro := (rsView_role hrv hok.facts.preRole).2
  refine ⟨.noReady v r₁ hri hob hrd (ht.trans hdt.1) (hv.trans hdt.2.1) (hc.trans hdt.2.2)
    (hrole.symm.trans hro) hfull, hfull, hfull, hrole.symm.trans hro⟩

/-- A loop head's view has nothing of a `Ready` left but its queue. -/
theorem reach_idle {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {net : List Msg} {xnet : List XMsg} {n : Fin R.N} {v : AntSim.NodeView} {r₁ : RState}
    (h : AntSim.Reach R dec Adm net xnet n v r₁) :
    v.pend = [] ∧ v.xpend = [] ∧ v.ce = [] ∧ v.rpend = [] :=
  match h with
  | .stay _ hI _ => hI.2
  | .input _ _ _ hI _ _ _ _ _ _ => hI.2
  | .advance _ _ h1 h2 h3 h4 _ _ _ => ⟨h1, h2, h3, h4⟩

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **A step that reports nothing moves the view** (`QuietIn`, `antSim_quiet_in`): node `j`'s view
`v` (between the sent lists' lower bounds `net₀`, `xnet₀` and the invariant's) becomes `v'`, whose
full log is `v`'s (so still certified), given the quiet step at the invariant's sent lists and
node `j`'s facts there (`hq`). -/
theorem view_quiet (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (msk : AntSim.SimMask) (h_quiet : antSim_quiet_in.law msk) (h_mask : runInMask.law msk)
    (γ : AntNames) (j : Fin γ.R.N) (v v' : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg)
    (hrun : InScope γ.scope γ.mode ∧ ModeRun γ.scope γ.mode γ.R) (hb1 : DrainB1 γ.scope γ.mode)
    {Adm : List EntryM → CCState → Prop} {P : Prop}
    (hq : ∀ (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView) (net : List Msg)
      (xnet : List XMsg), net₀ <+: net → xnet₀ <+: xnet → AntSim.InMask msk γ.R net xnet →
      AntSim.AntSim γ.R γ.dec S V net xnet → V j = v →
      AntSim.QuietIn msk γ.R γ.dec Adm net xnet j v v' ∧ v'.r.full = v.r.full ∧ P) :
    inv antN (antInv (GF := GF) γ) ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ viewFrag γ j v ∗
        nodeLive γ j ⊢
      |={⊤}=> viewFrag γ j v' ∗ nodeLive γ j ∗ ⌜P⌝ := by
  iintro ⟨#Hinv, #Hlb, #Hxlb, Hv, Hl⟩
  iunfold sentLb at Hlb
  iunfold xsentLb at Hxlb
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G, Hstr, Hviews, Hnet, Hxnet, %Hpure, #HF⟩
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    ihave %Hxpre := mono_list_auth_lb_valid (GF := GF) γ.xsent 1 xnet xnet₀ $$ Hxnet Hxlb
    imod h_vu (⊤ \ ↑antN) γ j V v v' $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    obtain ⟨hR, hL, hG, hlogs⟩ := Hpure
    have hin := h_mask γ evs S V net xnet hrun.1 hrun.2 hb1 hR
    obtain ⟨hP, hA, hB, hCB, hC⟩ := hR
    obtain ⟨hq', hfull, hPq⟩ := hq S V net xnet Hpre.2 Hxpre.2 hin hA HVj
    have hA' := h_quiet γ.R γ.dec S V net xnet G j v' hin hA hL hG (by rw [HVj]; exact hq')
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInv
      ileft
      iunfold antOpen
      iexists evs, S, AntSim.setV V j v', net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro
      refine ⟨⟨hP, hA', hB, hCB, hC⟩, hL, hG, ?_⟩
      intro i
      unfold AntSim.setV
      split
      · rw [hfull, ← HVj]; exact hlogs _
      · exact hlogs i
    imodintro
    iframe Hv Hl
    ipureintro; exact hPq
  · iexfalso
    iapply h_lo γ j
    iframe Hl Hover

/-- The run's initial voters' ids (`nodeOwn`'s storage and configuration). -/
abbrev votersW (γ : AntNames) : List w64 := (List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)

/-- **The loop head but the `RawNode`** (`nodeOwn`'s `.loop` phase at the client's record `rs`). -/
def loopRest (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg) (rs : RNState) : IProp GF :=
  iprop(∃ (d ms hsl cl csl : Loc) (role : GoString) (applied : w64) (si : Loc),
    n.[H.node, go!"disk"] ↦□ d ∗ nodeMemB1 n ∗
    n.[H.node, go!"store"] ↦ ms ∗ n.[H.node, go!"role"] ↦ role ∗
    n.[H.node, go!"hs"] ↦ hsl ∗ n.[H.node, go!"cause"] ↦ cl ∗ n.[H.node, go!"applied"] ↦ applied ∗
    n.[H.node, go!"conf"] ↦ csl ∗ viewFrag γ j v ∗ nodeLive γ j ∗ diskOwn d v.dur ∗
    nodeStor si ms (votersW γ) (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) ∗
    ⌜rs.storage = interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩⌝ ∗
    nodeRaft γ j rs ∗
    ⌜v.alive = true ∧ role = AntSim.roleS v ∧ uint.nat applied = v.delivered.length⌝ ∗
    hsRO hsl (HardStateM.mk v.dur.term v.dur.vote v.dur.commit) ∗
    csPts csl DFrac.discard (ConfStateM.mk (votersW γ) [] [] [] false) false ∗
    ⌜v.conf = γ.R.c0⌝ ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ causeOwn γ j v cl)

/-- **`nodeOwn`'s loop phase opened.** -/
theorem nodeOwn_loop_open (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) :
    nodeOwn (GF := GF) c γ j n v (.loop net₀ xnet₀ r₁ xs₁) ⊢
      ∃ (rn : Loc) (rs : RNState) (ip : Nat),
        n.[H.node, go!"rn"] ↦ rn ∗ rawNode γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs r₁ [] ip ∗
        ⌜RsView rs v ∧ AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j v r₁ ∧
          ip = lcpLen v.r.p.log r₁.p.log ∧ ByOk v.byE ∧ ViewNormal v ∧ rs.k = γ.R.k j⌝ ∗
        loopRest γ j n v net₀ xnet₀ rs := by
  unfold nodeOwn
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, #Hd, Hmem, Hrn, Hms, Hrole, Hhs, Hcause,
    Happ, Hconf, Hv, Hl, %HN, Hdisk, %si, %rs, %qs, %ip, %r, Hstor, %Hsto, Hraw, Hnr, %Hrv, #Hhsro,
    #Hcs, %Hc0, %Hph, #Hlb, #Hxlb, Hco⟩
  obtain ⟨rfl, hR, rfl, hip, hby⟩ := Hph
  iexists rn, rs, ip
  iframe Hrn Hraw
  isplitr
  · ipureintro; exact ⟨Hrv.1, hR, hip, hby, HN, Hrv.2.2.2.2⟩
  iunfold loopRest
  iexists d, ms, hsl, cl, csl, role, applied, si
  iframe Hd Hmem Hms Hrole Hhs Hcause Happ Hconf Hv Hl Hdisk Hstor Hnr Hhsro Hcs Hlb Hxlb Hco
  ipureintro
  exact ⟨Hsto, ⟨Hrv.2.1, Hrv.2.2.1, Hrv.2.2.2.1⟩, Hc0⟩

/-- **The loop's exit** (`HasReady` false at the loop head, no read state): the view moved to the
node's state (`QuietIn.noReady`, `view_quiet`), the node drained; the view's `by` kept. -/
theorem drain_exit (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (h_quiet : antSim_quiet_in.law AntSim.mskB1) (h_mask : runInMask.law AntSim.mskB1)
    (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (rn : Loc) (rs : RNState) (ip : Nat)
    (hrun : InScope γ.scope γ.mode ∧ ModeRun γ.scope γ.mode γ.R) (hb1 : DrainB1 γ.scope γ.mode)
    (hcc : γ.R.md.confChanges = false)
    (hrv : RsView rs v) (hR : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j v r₁)
    (hby : ByOk v.byE) (hN : ViewNormal v) (hk : rs.k = γ.R.k j)
    (hP : PIdle rs r₁.p) (hip : ip = r₁.p.log.length) (hrd : r₁.p.rd.states = []) :
    inv antN (antInv (GF := GF) γ) ∗ n.[H.node, go!"rn"] ↦ rn ∗
        rawNode γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs r₁ [] ip ∗
        loopRest γ j n v net₀ xnet₀ rs ⊢
      |={⊤}=> nodeOwn c γ j n { v with r := r₁, qs := [] } .drained := by
  iintro ⟨#Hinv, Hrn, Hraw, Hrest⟩
  iunfold loopRest at Hrest
  icases Hrest with ⟨%d, %ms, %hsl, %cl, %csl, %role, %applied, %si, #Hd, Hmem, Hms, Hrole, Hhs,
    Hcause, Happ, Hconf, Hv, Hl, Hdisk, Hstor, %Hsto, Hnr, %Hpv, #Hhsro, #Hcs, %Hc0, #Hlb, #Hxlb, Hco⟩
  imod view_quiet h_vu h_lo AntSim.mskB1 h_quiet h_mask γ j v { v with r := r₁, qs := [] } net₀ xnet₀
      hrun hb1 (Adm := AdmFold γ.dec γ.R.c0) (P := r₁.full = v.r.full ∧ r₁.p.role = v.ps.role)
      (fun S V net xnet hn hx hin hA hVj =>
        quiet_noReady hin hA hVj hcc hby hR hn hx hrv hP hrd)
      $$ [Hinv Hlb Hxlb Hv Hl] with ⟨Hv, Hl, %Hfr⟩
  · iframe Hinv Hlb Hxlb Hv Hl
  obtain ⟨hfull, hrole⟩ := Hfr
  have hidle := reach_idle hR
  have hroleS : AntSim.roleS { v with r := r₁, qs := [] } = AntSim.roleS v := by
    unfold AntSim.roleS; simp only [AntSim.NodeView.ps]; rw [hrole]
  imodintro
  unfold nodeOwn
  iexists d, rn, ms, hsl, cl, csl, role, applied
  iframe Hd Hmem Hrn Hms Hrole Hhs Hcause Happ Hconf Hv Hl
  isplitr
  · ipureintro; exact ⟨by simp only [AntSim.NodeView.r]; rw [hfull]; exact hN.1, hN.2⟩
  dsimp only
  iframe Hdisk
  iexists si, rs, [], ip, r₁
  rw [show causeOwn (GF := GF) γ j { v with r := r₁, qs := [] } cl = causeOwn γ j v cl from rfl]
  iframe Hstor Hraw Hnr Hhsro Hcs Hco
  have hrv' : RsView rs { v with r := r₁, qs := [] } := by
    refine ⟨hrv.1, hrv.2.1, hrv.2.2.1, hrv.2.2.2.1, hrv.2.2.2.2.1, hrv.2.2.2.2.2.1, ?_,
      hrv.2.2.2.2.2.2.2⟩
    rw [hroleS]; exact hrv.2.2.2.2.2.2.1
  isplitr
  · ipureintro; exact Hsto
  isplitr
  · ipureintro; exact ⟨hrv', Hpv.1, by rw [hroleS]; exact Hpv.2.1, Hpv.2.2, hk⟩
  isplitr
  · ipureintro; exact Hc0
  ipureintro
  exact ⟨⟨rfl, hidle⟩, rfl, rfl, hip, hP⟩

end laws

end AntHarness
end EtcdGrove
end Perennial
