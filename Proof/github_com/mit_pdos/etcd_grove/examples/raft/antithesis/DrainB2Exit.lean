/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E (the synchronous `node.drain`): **the
loop's ends under B2** (`DrainB1Loop.drain_exit`'s over `nodeOwnB2HD`):
- `nodeOwnB2HD_dead_drained`: a dead node's loop head is drained (a dead node's phase is only its
  arm's name);
- `nodeMemB2_D`: alive with synchronous storage, the durable ghost is the record's durable state;
- `view_noReadyB2`: `HasReady` false at the loop head moves the view to raft's state in the run's
  invariant (`antSim_noReadyD_in.law`);
- `drain_exitB2`: the loop head with `HasReady` false, drained.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Sync
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Loop
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Holds
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Quiet
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Loop
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.RunInMaskB2

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

theorem mskB2_le_self : AntSim.mskB2 ≤ AntSim.mskB2 := by
  simp [LE.le, AntSim.SimMask.Le, AntSim.RnMode.Le, AntSim.NodeK.Le, AntSim.BLe]

/-- B2's `RsViewB2` with synchronous storage is B1's `RsView`. -/
theorem rsView_of_b2 {md : H.Mode} {rs : RNState} {v : AntSim.NodeView} (h : RsViewB2 md rs v)
    (has : md.Async' = false) : RsView rs v := by
  obtain ⟨h3, h4, h6, h7, f⟩ := h
  obtain ⟨h1, h2, h5, h8⟩ := f has
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **A loop head with no `Ready` under B2** (`quiet_noReady`'s facts over `NodeOkD`): the node's state
has the view's hard state, role and full log, nothing to send or read. -/
theorem noReady_factsD {msk : AntSim.SimMask} (hmsk : msk ≤ AntSim.mskB2) {R : AntSim.RunCfg}
    {dec : CCDec} {Adm : List EntryM → CCState → Prop} {S : AntCheck.State} {net : List Msg}
    {xnet : List XMsg} {j : Fin R.N} {v : AntSim.NodeView} {r₁ : RState} {rs : RNState}
    (hin : AntSim.InMask msk R net xnet) (hbt : R.drv.batch = false)
    (hok : AntSim.NodeOkD R dec S net j v) (hm : v.mems = []) (hp : v.parts = [])
    (hri : AntSim.ReachIn msk R dec Adm net xnet j v r₁)
    (hrv : RsView rs v) (hP : PIdle rs r₁.p) :
    r₁.p.outbox = [] ∧ r₁.p.term = v.ps.term ∧ r₁.p.vote = v.ps.vote ∧ r₁.p.commit = v.ps.commit ∧
      r₁.p.role = v.ps.role ∧ r₁.full = v.r.full := by
  obtain ⟨hsn, -, -⟩ := AntSim.InMask.b2 hmsk hin
  have hsd := nodeOkD_dur hok hm hp
  have hfp := AntSim.reach_fpD hmsk hin hbt hok hri
  have hfp0 := ((nodeOkD_facts hok).2.1 hsn).2.1
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
  have hro := (rsView_role hrv (nodeOkD_facts hok).2.2.2.2.2.2.2.2.1).2
  exact ⟨hob, ht.trans hdt.1, hv.trans hdt.2.1, hc.trans hdt.2.2, hrole.symm.trans hro, hfull⟩

/-- A loop head's view has nothing of a `Ready` left but its queue (`reach_idle`'s over `ReachIn`). -/
theorem reachIn_idle {msk : AntSim.SimMask} {R : AntSim.RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {net : List Msg} {xnet : List XMsg} {n : Fin R.N}
    {v : AntSim.NodeView} {r₁ : RState} (h : AntSim.ReachIn msk R dec Adm net xnet n v r₁) :
    v.pend = [] ∧ v.xpend = [] ∧ v.ce = [] ∧ v.rpend = [] := by
  cases h with
  | stay hI _ => exact hI.2
  | input inp r₁ h0 hI h1 h2 h3 h4 h5 h6 => exact hI.2
  | advance r₁ h1 h2 h3 h4 h5 h6 h7 => exact ⟨h1, h2, h3, h4⟩

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **A dead node's loop head is drained** (a dead node's phase holds nothing but its arm's name). -/
theorem nodeOwnB2HD_dead_drained (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) :
    nodeOwnB2HD (GF := GF) c γ j n v (.loop net₀ xnet₀ r₁ xs₁) none true ⊢
      nodeOwnB2HD c γ j n v .drained none true := by
  unfold nodeOwnB2HD
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, %fuse, %dk, #Hd, Hrn, Hms, Hrole, Hhs,
    Hcause, Happ, Hconf, Hkill, Hv, Hdisk, %Hvd, %si, %rs, %qs, %ip, %r, %x, %g, %D, %hn, Hstor,
    %Hsto, Hraw, Hgv, Hdur, Htlb, Hbud, %HD, Hmem, #Hhsro, -⟩
  iexists d, rn, ms, hsl, cl, csl, role, applied, fuse, dk
  iframe Hd Hrn Hms Hrole Hhs Hcause Happ Hconf Hkill Hv Hdisk
  isplitr
  · ipureintro; exact Hvd
  iexists si, rs, qs, ip, r, x, g, D, hn
  iframe Hstor Hraw Hgv Hdur Htlb Hbud Hmem Hhsro
  isplitr
  · ipureintro; exact Hsto
  isplitr
  · ipureintro; exact HD
  simp only [ite_true]
  ipureintro; trivial

/-- **Alive with synchronous storage, the durable ghost is the record's durable state** (`JobsChain`
over no job). -/
theorem nodeMemB2_D (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (x : CrashNames) (g : Nat) (phs : HardStateM) (dur D : RaftState)
    (has : γ.mode.Async' = false) :
    nodeMemB2 (GF := GF) γ j n v x g phs dur D false none ⊢
      ⌜D = dur⌝ ∗ nodeMemB2 γ j n v x g phs dur D false none := by
  unfold nodeMemB2
  iintro ⟨%items, %mhs, %rhs, %wip, %aip, %wsl, %asl, %wls, %als, %jobs, %ajobs, %ow, %oa, %hm', %rh,
    H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, Hm, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22,
    %Hp⟩
  have hD : D = dur := by
    obtain ⟨-, h2, -, -, -, -, -, h8⟩ := Hp
    obtain ⟨hj, hw, -, -⟩ := h8 has
    have h := h2 rfl
    subst hj; subst hw
    exact h
  isplitr
  · ipureintro; exact hD
  iexists items, mhs, rhs, wip, aip, wsl, asl, wls, als, jobs, ajobs, ow, oa, hm', rh
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 Hm H13 H14 H15 H16 H17 H18 H19 H20 H21 H22
  ipureintro; exact Hp

/-- **A loop head with no `Ready` in the run's invariant** (`antSim_noReadyD_in.law`): at a view with
no `mem` record and no split write, reached from the sent lists' lower bounds, the view takes raft's
state. -/
theorem view_noReadyB2 (h_vu : view_update.law (GF := GF)) (h_nr : antSim_noReadyD_in.law)
    (msk : AntSim.SimMask) (hmsk : msk ≤ AntSim.mskB2) (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N)
    (q : Qp) (v : AntSim.NodeView) (r₁ : RState) (rs : RNState) (net₀ : List Msg) (xnet₀ : List XMsg)
    {Adm : List EntryM → CCState → Prop}
    (hinm : ∀ S V net xnet, AntSim.AntSimD γ.R γ.dec S V net xnet → AntSim.InMask msk γ.R net xnet)
    (has : γ.R.md.async = false) (hbt : γ.R.drv.batch = false)
    (hm : v.mems = []) (hparts : v.parts = [])
    (hreach : AntSim.ReachIn msk γ.R γ.dec Adm net₀ xnet₀ j v r₁)
    (hrv : RsView rs v) (hP : PIdle rs r₁.p) (hrd : r₁.p.rd.states = []) :
    antClusterB2 (GF := GF) c γ ∗ sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗
        viewFrag γ.toAntNames j v ∗ runLive γ q ⊢
      |={⊤}=> ⌜r₁.full = v.r.full ∧ r₁.p.role = v.ps.role⌝ ∗
        viewFrag γ.toAntNames j { v with r := r₁, qs := [] } ∗ runLive γ q := by
  iintro ⟨#Hc, #Hlb, #Hxlb, Hv, Hl⟩
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, -, -, -, -, -, -, #Hinv, %Hrf, -⟩
  iunfold sentLb at Hlb
  iunfold xsentLb at Hxlb
  iinv Hinv with >Hi Hclose
  iunfold antInvB2 at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpenB2 at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G, Hstr, Hviews, Hnet, Hxnet, %Hpure, #HF⟩
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    ihave %Hxpre := mono_list_auth_lb_valid (GF := GF) γ.xsent 1 xnet xnet₀ $$ Hxnet Hxlb
    imod h_vu (⊤ \ ↑antN) γ.toAntNames j V v { v with r := r₁, qs := [] } $$ [Hv Hviews] with
      ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    obtain ⟨⟨hP', hA, hB, hCB, hC⟩, hL, hG0, hlogs⟩ := Hpure
    have hin := hinm S V net xnet hA
    subst HVj
    have hri := hreach.mono Hpre.2 Hxpre.2
    obtain ⟨hob, ht, hvo, hcm, hrl, hfull⟩ :=
      noReady_factsD hmsk hin hbt (hA.2.2.2.2 j) hm hparts hri hrv hP
    have hA' := h_nr msk hmsk γ.R γ.dec S V net xnet G j r₁ Adm hin hA hL hG0 has hbt hm hparts hri
      hob hrd ht hvo hcm hrl hfull
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInvB2
      ileft
      iunfold antOpenB2
      iexists evs, S, AntSim.setV V j { V j with r := r₁, qs := [] }, net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro
      refine ⟨⟨hP', hA', hB, hCB, hC⟩, hL, hG0, ?_⟩
      intro i
      unfold AntSim.setV
      split
      · show r₁.full ∈ G.logs
        rw [hfull]; exact hlogs j
      · exact hlogs i
    imodintro
    iframe Hv Hl
    ipureintro; exact ⟨hfull, hrl⟩
  · iexfalso
    iapply runLive_excl γ q
    iframe Hl Hover

/-- **`HasReady` false at a loop head under B2** (synchronous storage, no batching): the view moved
to the node's state (`view_noReadyB2`), the node drained. -/
theorem drain_exitB2 (h_vu : view_update.law (GF := GF)) (h_nr : antSim_noReadyD_in.law)
    (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (q : Qp) (v : AntSim.NodeView)
    (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (rn : Loc) (rs : RNState) (qs : List Msg)
    (ip : Nat) (x : CrashNames) (g : Nat) (D : RaftState) (hsl : Loc)
    (hmr : ModeRun γ.scope γ.mode γ.R) (hb2 : DrainB2 γ.scope γ.mode)
    (has : γ.mode.Async' = false) (hbt : γ.mode.Batch' = false)
    (hrv : RsViewB2 γ.mode rs v)
    (hR : AntSim.ReachIn AntSim.mskB2 γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j v r₁)
    (hqs : qs = []) (hk : rs.k = γ.R.k j)
    (hP : PIdle rs r₁.p) (hip : ip = r₁.p.log.length) (hrd : r₁.p.rd.states = []) :
    antClusterB2 (GF := GF) c γ ∗ runLive γ q ∗ n.[H.node, go!"rn"] ↦ rn ∗
        rawNode γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs r₁ qs ip ∗
        genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗
        ownDurGhost γ.raft.raftNames (AntSim.nodeId j) D ∗
        (⌜γ.mode.Async' = true⌝ ∨ slotFree γ.raft.raftNames (AntSim.nodeId j) g) ∗
        loopRestB2 γ j n v net₀ xnet₀ rs x g D hsl ⊢
      |={⊤}=> runLive γ q ∗ nodeOwnB2HD c γ j n { v with r := r₁, qs := [] } .drained none false := by
  iintro ⟨#Hc, Hl, Hrn, Hraw, Hgv, Hdur, Hslot, Hrest⟩
  iunfold loopRestB2 at Hrest
  icases Hrest with ⟨%d, %ms, %cl, %csl, %role, %applied, %fuse, %dk, %si, %hn, #Hd, Hms, Hrole,
    Hhs, Hcause, Happ, Hconf, Hkill, Hv, Hdisk, %Hvd, Hstor, %Hsto, Htlb, Hbud, %HD, Hmem, #Hhsro,
    %Hpv, #Hcs, Hrq, %Hc0, #Hlb, #Hxlb, Hco⟩
  icases nodeMemB2_mems_nil γ j n v x g rs.phs rs.dur D has hbt $$ Hmem with ⟨%Hmn, Hmem⟩
  icases nodeMemB2_D γ j n v x g rs.phs rs.dur D has $$ Hmem with ⟨%HDd, Hmem⟩
  have hasR : γ.R.md.async = false := by rw [hmr.2.2.2.2.1]; exact has
  have hbtR : γ.R.drv.batch = false := by rw [hmr.2.2.2.2.2]; exact hbt
  have hinm := inMask_b2_run (dec := γ.dec) hmr hb2 has hb2.2.2.2.2
  have hparts : v.parts = [] := (Hpv.2.2.2.2 has).2.2
  have hrv1 := rsView_of_b2 hrv has
  imod view_noReadyB2 h_vu h_nr AntSim.mskB2 mskB2_le_self c γ j q v r₁ rs net₀ xnet₀ hinm hasR hbtR
    Hmn hparts hR hrv1 hP hrd $$ [$Hc $Hlb $Hxlb $Hv $Hl] with ⟨%Hfr, Hv, Hl⟩
  obtain ⟨hfull, hrl⟩ := Hfr
  have hidle := reachIn_idle hR
  have hroleS : AntSim.roleS { v with r := r₁, qs := [] } = AntSim.roleS v := by
    unfold AntSim.roleS; simp only [AntSim.NodeView.ps]; rw [hrl]
  ihave Hmem := nodeMemB2_view γ j n v { v with r := r₁, qs := [] } x g rs.phs rs.phs rs.dur D rs.dur D
    false none has hbt (fun _ => ⟨Hmn, HDd⟩) $$ Hmem
  imodintro
  iframe Hl
  unfold nodeOwnB2HD
  iexists d, rn, ms, hsl, cl, csl, role, applied, fuse, dk
  iframe Hd Hrn Hms Hrole Hhs Hcause Happ Hconf Hkill Hv Hdisk
  isplitr
  · ipureintro
    refine ⟨?_, ?_,
      fun h => ⟨rfl, Hvd.2.2 h⟩⟩
    · have hv := Hvd.1
      unfold ViewNormal at hv ⊢
      simp only at hv ⊢
      rw [hfull]; exact hv
    rcases Hvd.2.1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  subst hqs
  iexists si, rs, [], ip, r₁, x, g, D, hn
  rw [show causeOwn (GF := GF) γ.toAntNames j { v with r := r₁, qs := [] } cl =
      causeOwn γ.toAntNames j v cl from rfl,
    show readsOwn (GF := GF) γ.toAntNames { v with r := r₁, qs := [] } = readsOwn γ.toAntNames v from rfl]
  iframe Hstor Hraw Hgv Hdur Htlb Hbud Hmem Hhsro
  isplitr
  · ipureintro; exact Hsto
  isplitr
  · ipureintro; exact HD
  simp only [Bool.false_eq_true, ite_false]
  iframe Hslot Hcs Hrq
  isplitr
  · ipureintro
    refine ⟨⟨hrv.1, hrv.2.1, hrv.2.2.1, by rw [hroleS]; exact hrv.2.2.2.1, hrv.2.2.2.2⟩, Hpv.1,
      by rw [hroleS]; exact Hpv.2.1, Hpv.2.2.1, Hpv.2.2.2.1⟩
  isplitr
  · ipureintro; exact Hc0
  iframe Hco
  ipureintro
  exact ⟨⟨rfl, hidle⟩, trivial, fun _ => hP, fun _ => ⟨trivial, hip⟩, fun h => (Hpv.2.2.2.2 h).1⟩

end laws

end AntHarness
end EtcdGrove
end Perennial
