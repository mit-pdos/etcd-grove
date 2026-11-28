/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E (`node.parallel`): **a `-parallel`
leader's `Ready` the harness does not report** (no write, the same role) moves node `j`'s view in the
run's invariant (`antInvB2`) without a report, through `AntSim.antSim_quietP_in` (B1's
`DrainB1Loop.view_quiet` over B2's invariant): the drain phase, its requests pending first; and
`writes_iff`, Go's `write` (`hs != n.hs || len(rd.Entries) > 0`) as the Sim's `Writes`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Cause
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.QuietP
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Mono
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **Go's `write` is the Sim's `Writes`** (`reported_iff`'s without the role): a new hard state
(one that differs from the disk's) or entries. -/
theorem writes_iff {v : AntSim.NodeView} {rs : RNState} {r : RState} {h : HardStateM} {s : w64}
    {es ce : List EntryM} {ms : List QMsg} {qs : List Msg} {sts : List ReadStateM}
    (hRs : RsView rs v)
    (hph : phsNext rs.phs h = HardStateM.mk r.p.term r.p.vote r.p.commit)
    (hne : HsNew h → h ≠ rs.phs) :
    (HsNew h ∨ es ≠ []) ↔ AntSim.Writes v (readyDOf r s es ce ms qs sts) := by
  have hphs := hRs.1
  unfold AntSim.Writes
  simp only [readyDOf]
  by_cases hn : HsNew h
  · have hh : h = HardStateM.mk r.p.term r.p.vote r.p.commit := by
      rw [← hph]; unfold phsNext HsNew at *; simp only [hn, ↓reduceIte]
    have hd := hne hn
    rw [hh, hphs] at hd
    have : r.p.term ≠ v.dur.term ∨ r.p.vote ≠ v.dur.vote ∨ r.p.commit ≠ v.dur.commit := by
      refine Classical.byContradiction fun hc => ?_
      simp only [not_or, Classical.not_not] at hc
      exact hd (by rw [hc.1, hc.2.1, hc.2.2])
    constructor
    · intro _
      rcases this with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
    · intro _; exact Or.inl hn
  · have hh : phsNext rs.phs h = rs.phs := by
      unfold phsNext HsNew at *; simp only [Classical.not_not.mp hn, and_self, ↓reduceIte]
    rw [hh, hphs] at hph
    simp only [HardStateM.mk.injEq] at hph
    obtain ⟨h1, h2, h3⟩ := hph
    rw [← h1, ← h2, ← h3]
    simp [hn]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The view after a `-parallel` leader's unreported `Ready`**: the drain phase, its requests
pending first, in their order, then the others in theirs. -/
abbrev quietPView (v : AntSim.NodeView) (r₁ : RState) (rd : AntSim.ReadyD) : AntSim.NodeView :=
  { (v.drainOf r₁ rd) with
    pend := rd.msgs.filter AntSim.isReqM ++ rd.msgs.filter (fun q => !AntSim.isReqM q) }

/-- **A `-parallel` leader's unreported `Ready` in the run's invariant** (`antSim_quietP_in`): at a
view with no `mem` record and no split write, reached from the sent lists' lower bounds, the view
moves to `quietPView`; raft's facts grow to the `Ready`'s (`factsExt`, as a report's). -/
theorem view_quietPB2 (h_vu : view_update.law (GF := GF)) (msk : AntSim.SimMask)
    (hmsk : msk ≤ AntSim.mskB2) (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp)
    (v : AntSim.NodeView) (r₁ : RState) (rd : AntSim.ReadyD) (net₀ : List Msg) (xnet₀ : List XMsg)
    {Adm : List EntryM → CCState → Prop}
    (hinm : ∀ S V net xnet, AntSim.AntSimD γ.R γ.dec S V net xnet → AntSim.InMask msk γ.R net xnet)
    (has : γ.R.md.async = false) (hbt : γ.R.drv.batch = false) (hpar : γ.R.drv.parallel = true)
    (hm : v.mems = []) (hparts : v.parts = [])
    (hreach : AntSim.ReachIn msk γ.R γ.dec Adm net₀ xnet₀ j v r₁)
    (hout : AntSim.ReadyOutP γ.R j v r₁ rd) (hlead : rd.role = .leader) (hsnap : rd.snap = none)
    (hrep : ¬ AntSim.Reported v rd) :
    antClusterB2 (GF := GF) c γ ∗ sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗
        □ factsExt γ.toAntNames (fun G0 G => FactsLe γ.R G0 G ∧ AntSim.RaftLaws G ∧
          AntSim.ReadyFacts G (AntSim.nodeId j) r₁) ∗
        viewFrag γ.toAntNames j v ∗ runLive γ q ⊢
      |={⊤}=> viewFrag γ.toAntNames j (quietPView v r₁ rd) ∗ runLive γ q := by
  iintro ⟨#Hc, #Hlb, #Hxlb, #Hext, Hv, Hl⟩
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, -, -, -, -, -, -, #Hinv, %Hrf, -⟩
  iunfold sentLb at Hlb
  iunfold xsentLb at Hxlb
  iinv Hinv with >Hi Hclose
  iunfold antInvB2 at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpenB2 at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G0, Hstr, Hviews, Hnet, Hxnet, %Hpure, #HF0⟩
    iunfold factsExt at Hext
    imod Hext $$ %G0 %Hpure.2.1 HF0 with ⟨%G, #HF, %HQ⟩
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    ihave %Hxpre := mono_list_auth_lb_valid (GF := GF) γ.xsent 1 xnet xnet₀ $$ Hxnet Hxlb
    imod h_vu (⊤ \ ↑antN) γ.toAntNames j V v (quietPView v r₁ rd) $$ [Hv Hviews] with
      ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    obtain ⟨⟨hP, hA, hB, hCB, hC⟩, -, hG0, hlogs⟩ := Hpure
    obtain ⟨hle, hL, hRF⟩ := HQ
    have hin := hinm S V net xnet hA
    subst HVj
    have hA' := AntSim.antSim_quietP_in msk hmsk γ.R γ.dec S V net xnet G j r₁ rd Adm hin hA hL
      (globalOk_mono hG0 hle) has hbt hpar hm hparts (hreach.mono Hpre.2 Hxpre.2) hout hlead hsnap
      hrep hRF
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInvB2
      ileft
      iunfold antOpenB2
      iexists evs, S, AntSim.setV V j (quietPView (V j) r₁ rd), net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro
      refine ⟨⟨hP, hA', hB, hCB, hC⟩, hL, globalOk_mono hG0 hle, ?_⟩
      intro i
      unfold AntSim.setV
      split
      · exact hRF.1
      · exact hle.2.2.2.1 _ (hlogs i)
    imodintro
    iframe Hv Hl
  · iexfalso
    iapply runLive_excl γ q
    iframe Hl Hover

end proof

end AntHarness
end EtcdGrove
end Perennial
