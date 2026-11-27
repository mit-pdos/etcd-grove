/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **`reportCause`'s reports under B2**
(`DrainB1Report.causeOwn_report` over `antClusterB2`, the run's liveness share for the node's `live`):
- `AntSim.antSim_recvXD_in`: a transfer message's `recv` over `AntSimD` (`antSim_recvX_in`'s, as
  `Sim/CarryD`'s `antSim_recvD_in` is `recv`'s), without batching;
- `causeOwn_reportB2`: the cause cell's pending report and `reports` of it, through the run's invariant
  (`report_updB2`), the view `told` after;
- `causeOwn_pendingB2`: the cause cell's pending report alone (a kill: nothing is recorded, the view
  is kept).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Report
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReportB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.XMsgs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntSim

open go_etcd_io.raft.v3 AntCheck

section carryd
variable [GooseExts]

/-- **`recv` of a transfer message** over `AntSimD` (`antSim_recvX_in`'s), for every mask below
`mskB2`, without batching. -/
theorem antSim_recvXD_in (msk : SimMask) (_hmsk : msk ≤ mskB2) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (x : XMsg),
      InMask msk R net xnet → R.drv.batch = false →
      SimPreD R dec S V net xnet evs G → x ∈ xnet → x.dst = nodeId n → (V n).xcause = some x →
      SimStepD R dec evs G (evRecvX (nodeId n) x) (setV V n { V n with told := true }) net xnet := by
  intro R dec S V net xnet evs G n x _ hbat ⟨hp, hs, hl, hgo⟩ _ hdst hxc
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gcD hbat hs hl hgo
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  have hstep := recvX_eq n x hc hdst
  have hrel : AntSimD R dec (recvS S1 n.val (xmsgOf x)) (setV V n { V n with told := true }) net
      xnet := by
    obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11,
      by simpa [recvS] using sh12, sh13, sh14⟩, hb, hn, hxn, fun k => ?_⟩
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20⟩ :=
      hno k
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, fun _ => .inr ⟨x, hxc, ?_⟩,
        d16, d17, d18, d19, d20⟩
      change (S1.pending.set k.val [xmsgOf x])[k.val]! = _
      exact get!_set_self _ (by rw [sh12]; exact k.isLt)
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, fun ht => ?_, d16, d17, d18,
        d19, d20⟩
      rw [show (recvS S1 n.val (xmsgOf x)).pending[k.val]! = S1.pending[k.val]! from
        get!_set_ne _ _ hne]
      exact d15 ht
  have hgo2 : GlobalOk R (recvS S1 n.val (xmsgOf x)) net G := hgo1
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1.1 hl hgo2), hrel, hgo2⟩

end carryd

end AntSim

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

/-- **The cause cell's pending report** (a kill: nothing recorded): `reportCause`'s `pendingCause`,
some exactly while the view's `recv` is not reported. -/
theorem causeOwn_pendingB2 (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView) (cl : Loc) :
    causeOwn (GF := GF) γ j v cl ⊢
      ∃ o : Option AntCheck.Event, pendingCause cl o ∗
        ⌜o.isSome = decide (v.byE = go!"recv" ∧ v.told = false)⌝ := by
  unfold causeOwn
  by_cases hp : v.byE = go!"recv" ∧ v.told = false
  · rw [if_pos hp]
    iintro (⟨%m, -, Hpc, -, -⟩ | ⟨%x, -, Hpc, -, -⟩)
    · iexists some (recvEvM (AntSim.msgOf m (AntSim.nodeId j)))
      iframe Hpc; ipureintro; simp [hp]
    · iexists some (recvEvM (AntSim.xmsgOf x))
      iframe Hpc; ipureintro; simp [hp]
  · rw [if_neg hp]
    iintro Hpc
    iexists none
    iframe Hpc; ipureintro; simp [hp]

/-- **`reportCause`'s reports under B2** (`causeOwn_report`'s): from the cause cell against the view,
the pending report `o` (some exactly while the view's `recv` is not reported) and `reports` of it: the
handled message's `recv` (`antSim_recvD_in` / `antSim_recvXD_in`), or nothing; the caller's `Φ` at the
view with `told` set as `Told` needs, the sent lists' lower bounds grown. -/
theorem causeOwn_reportB2 (h_vu : view_update.law (GF := GF)) (msk : AntSim.SimMask)
    (hmsk : msk ≤ AntSim.mskB2)
    (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg) (cl : Loc) (Φ : IProp GF) (hbat : γ.R.drv.batch = false)
    (hinm : ∀ S V net xnet, AntSim.AntSimD γ.R γ.dec S V net xnet →
      AntSim.InMask msk γ.R net xnet) :
    antClusterB2 c γ ∗ sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗
        causeOwn γ.toAntNames j v cl ∗ viewFrag γ.toAntNames j v ∗ runLive γ q ∗
        (∀ (b : Bool) (net : List Msg) (xnet : List XMsg),
          ⌜(v.byE = go!"recv" → b = true) ∧ net₀ <+: net ∧ xnet₀ <+: xnet⌝ -∗
            sentLb γ.toAntNames net -∗ xsentLb γ.toAntNames xnet -∗
            viewFrag γ.toAntNames j { v with told := b } -∗ runLive γ q -∗ Φ) ⊢
      ∃ o : Option AntCheck.Event, pendingCause cl o ∗
        ⌜o.isSome = decide (v.byE = go!"recv" ∧ v.told = false)⌝ ∗
        reports γ.strm (o.toList.map (atNode (AntSim.nameOf (AntSim.nodeId j)))) Φ := by
  iintro ⟨#Hc, #Hlb, #Hxlb, Hco, Hv, Hl, HΦ⟩
  unfold causeOwn
  by_cases hp : v.byE = go!"recv" ∧ v.told = false
  · rw [if_pos hp]
    icases Hco with (⟨%m, %Hm, Hpc, #Hw, Hr⟩ | ⟨%x, %Hx, Hpc, #Hw, Hr⟩)
    · ihave ⟨%net₁, #Hlb1, %Hn1⟩ := sentLb_join γ.toAntNames net₀ m $$ [$Hw $Hlb]
      iexists some (recvEvM (AntSim.msgOf m (AntSim.nodeId j)))
      iframe Hpc
      isplitr
      · ipureintro; simp [hp]
      have hev : atNode (AntSim.nameOf (AntSim.nodeId j)) (recvEvM (AntSim.msgOf m (AntSim.nodeId j))) =
          AntSim.evRecv (AntSim.nodeId j) m := rfl
      simp only [Option.toList, List.map_cons, List.map_nil, hev]
      iapply report_updB2 h_vu c γ j q v { v with told := true } (AntSim.evRecv (AntSim.nodeId j) m)
        net₁ [] xnet₀ [] (fun G0 G => G = G0) Φ Hm.2.2 (evRecv_chgOk _ _)
      · intro evs S V net xnet G0 G hpre hlogs hQ hVj hn hx
        subst hQ
        refine ⟨?_, hpre.2.2.1, ?_⟩
        · simp only [List.append_nil]
          have := AntSim.antSim_recvD_in msk hmsk γ.R γ.dec S V net xnet evs G j m
            (hinm S V net xnet hpre.2.1) hbat hpre (hn.subset Hn1.2) Hm.2.1 (by rw [hVj]; exact Hm.1)
          rw [hVj] at this; exact this
        · exact setV_logs hlogs (fun _ h => h) (by rw [← hVj]; exact hlogs j)
      iframe Hc Hlb1 Hxlb Hr Hv Hl
      isplitr
      · iapply factsExt_none
      iintro ⟨Hv, Hl, %net, %xnet, #Hlb2, #Hxlb2, %Hp2⟩
      iapply HΦ $$ %true %net %xnet [] Hlb2 Hxlb2 Hv Hl
      ipureintro; exact ⟨fun _ => rfl, Hn1.1.trans Hp2.1, Hp2.2.2.1⟩
    · ihave ⟨%xnet₁, #Hxlb1, %Hx1⟩ := xsentLb_join γ.toAntNames xnet₀ x $$ [$Hw $Hxlb]
      iexists some (recvEvM (AntSim.xmsgOf x))
      iframe Hpc
      isplitr
      · ipureintro; simp [hp]
      have hev : atNode (AntSim.nameOf (AntSim.nodeId j)) (recvEvM (AntSim.xmsgOf x)) =
          AntSim.evRecvX (AntSim.nodeId j) x := rfl
      simp only [Option.toList, List.map_cons, List.map_nil, hev]
      iapply report_updB2 h_vu c γ j q v { v with told := true } (AntSim.evRecvX (AntSim.nodeId j) x)
        net₀ [] xnet₁ [] (fun G0 G => G = G0) Φ Hx.2.2 (evRecvX_chgOk _ _)
      · intro evs S V net xnet G0 G hpre hlogs hQ hVj hn hx
        subst hQ
        refine ⟨?_, hpre.2.2.1, ?_⟩
        · simp only [List.append_nil]
          have := AntSim.antSim_recvXD_in msk hmsk γ.R γ.dec S V net xnet evs G j x
            (hinm S V net xnet hpre.2.1) hbat hpre (hx.subset Hx1.2) Hx.2.1 (by rw [hVj]; exact Hx.1)
          rw [hVj] at this; exact this
        · exact setV_logs hlogs (fun _ h => h) (by rw [← hVj]; exact hlogs j)
      iframe Hc Hlb Hxlb1 Hr Hv Hl
      isplitr
      · iapply factsExt_none
      iintro ⟨Hv, Hl, %net, %xnet, #Hlb2, #Hxlb2, %Hp2⟩
      iapply HΦ $$ %true %net %xnet [] Hlb2 Hxlb2 Hv Hl
      ipureintro; exact ⟨fun _ => rfl, Hp2.1, Hx1.1.trans Hp2.2.2.1⟩
  · rw [if_neg hp]
    iexists none
    iframe Hco
    isplitr
    · ipureintro; simp [hp]
    simp only [Option.toList, List.map_nil, reports]
    iapply HΦ $$ %v.told %net₀ %xnet₀ [] Hlb Hxlb Hv Hl
    ipureintro
    refine ⟨fun hb => ?_, List.prefix_refl _, List.prefix_refl _⟩
    cases ht : v.told
    · exact absurd ⟨hb, ht⟩ hp
    · rfl

end proof

end AntHarness
end EtcdGrove
end Perennial
