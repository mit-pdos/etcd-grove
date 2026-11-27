/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E: **the drain's `Ready` read at the
loop head** (node.drain's report `if`): `drain_peekRecsB1` (the run's invariant at the node's view:
its relation's facts at sent lists past the caller's lower bounds, the view's full log certified),
`readyOutP_b1` (raft's `Ready` post is the Sim's `ReadyOutP` there, `readyOutP_of` with the facts the
invariant gives).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Phases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Ext
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgShape

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **Raft's `Ready` at a loop head is the Sim's `ReadyOutP`** (`readyOutP_of`), with what the run's
relation gives at sent lists past the loop head's (`ReachIn`, `NodeOk`, `NetOk`): the view's disk its
protocol log (`SyncDisk`), no ghost prefix (`reach_fp`, `snap0`), the messages' destinations servers
(`dst_reach`), log matching from the two logs' records (`logMatch_of_recs`). The transfer messages'
`XPendOk` (`hx`) is the caller's (`xPendOk_of` over their certificates). Also: the node's full log is
its protocol log. -/
theorem readyOutP_b1 {R : AntSim.RunCfg} {dec : CCDec} {Adm : List EntryM → CCState → Prop}
    {S : AntCheck.State} {net : List Msg} {xnet : List XMsg} {j : Fin R.N} {v : AntSim.NodeView}
    {rs : RNState} {r : RState} {h : HardStateM} {es ce : List EntryM} {ms : List QMsg}
    {ss : Option (w64 × StateType)} {qs : List Msg} {sts : List ReadStateM} {ip : Nat}
    (hin : AntSim.InMask AntSim.mskB1 R net xnet) (hnet : AntSim.NetOk R S net)
    (hok : AntSim.NodeOk R dec S net j v) (hri : AntSim.ReachIn AntSim.mskB1 R dec Adm net xnet j v r)
    (hrv : RsView rs v) (hip : ip = lcpLen v.r.p.log r.p.log)
    (hout : ReadyOut (AntSim.nodeId j) rs r.p h es ce ms ss none)
    (hfirst : ∀ e0 ∈ es.head?, uint.nat e0.Index' = ip + 1)
    (hqs : qs.Perm (r.p.outbox.filter (fun m => decide (m.dst = AntSim.nodeId j))))
    (hpk : roleAfter rs.role ss = StatePreCandidate → (R.k j).prevote = true)
    (hx : ∀ x ∈ ms.filterMap (fun q => xmsgOf q.st), AntSim.XPendOk R.N (AntSim.nodeId j) r.p x)
    (hsts : sts = r.p.rd.states)
    (hns : r.p.base = base0 ∧ ∀ m ∈ r.p.outbox, m.ty ≠ .snap)
    (hwf : PlogWf base0 r.p.log) (hvidx : AntSim.LogIdx v.r.full)
    (hag : RecsAgree base0 v.r.full base0 r.p.log) :
    AntSim.ReadyOutP R j v r (readyDOf r (roleAfter rs.role ss) es ce ms qs sts) ∧
      r.full = r.p.log ∧ v.r.full = v.r.p.log ∧ v.dur.log = v.r.full := by
  obtain ⟨hmd, hbt, hpar, hspl, -, -⟩ := hin.b1 mskB1_le
  have hsn : R.md.snapshots = false := by rw [hmd]
  have hsd := (hok.sync (by rw [hmd]) hbt hspl hpar).2.1
  have hfp := AntSim.reach_fp mskB1_le hin hok hri
  have hfp0 := (hok.facts.snap0 hsn).2.1
  have hfull : r.full = r.p.log := by simp [RState.full, hfp, hfp0]
  have hvfull : v.r.full = v.r.p.log := by simp [RState.full, hfp0]
  have hdl : v.dur.log = v.r.full := by rw [hsd]; rfl
  have hidx := logIdx_of_wf hwf
  have hds := AntSim.dst_reach mskB1_le hin hnet hok hri
  refine ⟨readyOutP_of hrv (reach_ce hri.reach) (hfp.trans hfp0) (hdl.trans hvfull) hip hout hfirst hqs hpk
    (by rw [hmd]) hx hsts (fun _ => hns) (by rw [hfull]; exact hidx) ?_ ?_, hfull, hvfull, hdl⟩
  · intro k e f he hf ht
    rw [hdl] at he
    rw [hfull] at hf
    have htk := logMatch_of_recs hvidx hidx hag k e f he hf ht
    have h1 : (v.r.full.take (k + 1))[k]? = some e := by
      rw [List.getElem?_take]; simp [he]
    have h2 : (r.p.log.take (k + 1))[k]? = some f := by
      rw [List.getElem?_take]; simp [hf]
    rw [htk, h2] at h1
    exact (Option.some.inj h1).symm
  · intro q hq
    have hq' := (hout.2.2.2.2.1.mem_iff).mp hq
    rw [List.mem_filter] at hq'
    exact hds q hq'.1 (of_decide_eq_true hq'.2)

/-- The Sim's role string of a `Ready`'s view is Go's role string of the role after it. -/
theorem roleS_drainOf {v : AntSim.NodeView} {rs : RNState} {r : RState} {h : HardStateM}
    {es ce : List EntryM} {ms : List QMsg} {ss : Option (w64 × StateType)} {qs : List Msg}
    {sts : List ReadStateM} {id : w64} (hout : ReadyOut id rs r.p h es ce ms ss none) :
    AntSim.roleS (v.drainOf r (readyDOf r (roleAfter rs.role ss) es ce ms qs sts)) =
      roleStr (roleAfter rs.role ss) := by
  rw [← readyDOf_roleStr (es := es) (ce := ce) (ms := ms) (qs := qs) (sts := sts) hout.1.1]
  rfl

/-- **The view after a reported `Ready`** (`afterReady`) against the record after it and the
write's handshake (`rs₂`, its steps for `Advance`), its entries normal. -/
theorem drainView_rep {I : DrainIterB1} {id : w64} (b : Bool)
    (hrv : RsView I.rs I.v) (hce : I.v.ce = [])
    (hout : ReadyOut id I.rs I.r.p I.h I.es I.ce I.ms I.ss none) (hfull : I.r.full = I.r.p.log)
    (hN : ViewNormal I.v) (hnorm : AllNormal I.r.full) :
    RsView { I.rs₂ with steps := [] } ({ I.v with told := b }.afterReady I.r
        (readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts)) ∧
      ViewNormal ({ I.v with told := b }.afterReady I.r
        (readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts)) := by
  obtain ⟨-, -, hdel, -, -, hflw, -, -⟩ := hrv
  have hph := hout.2.1
  have hents := hout.2.2.1
  have hrole := roleS_drainOf (v := { I.v with told := b }) (qs := I.qs) (sts := I.sts) hout
  refine ⟨⟨?_, ?_, ?_, rfl, rfl, hflw, ?_, ?_⟩, ?_, hN.2⟩
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.afterReady, AntSim.durOf, AntSim.accepted]; exact hph
  · show (readyDurable I.rs.dur (phsNext I.rs.phs I.h) none I.es).ents = (AntSim.accepted I.r).full
    rw [hents]; exact hfull.symm
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.afterReady, AntSim.NodeView.drainOf, readyDOf]
    rw [hdel, hce]; simp
  · exact hrole.symm
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.afterReady, AntSim.durOf, AntSim.accepted,
      readyDurable, RaftState.next]
    have := congrArg HardStateM.Term' hph
    simpa using this
  · simpa [AntSim.NodeView.afterReady, AntSim.NodeView.drainOf, AntSim.accepted, RState.full] using hnorm

/-- **The view after a silent `Ready`** (`drainOf`: no hard state, no entries) against the record
after it (`rs₂`, its steps for `Advance`), its entries normal. -/
theorem drainView_silent {I : DrainIterB1} {id : w64}
    (hrv : RsView I.rs I.v) (hce : I.v.ce = [])
    (hout : ReadyOut id I.rs I.r.p I.h I.es I.ce I.ms I.ss none) (hfv : I.r.full = I.v.r.full)
    (hN : ViewNormal I.v) (hn : ¬ HsNew I.h) (hes : I.es = []) :
    RsView { I.rs₂ with steps := [] } (I.v.drainOf I.r
        (readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts)) ∧
      ViewNormal (I.v.drainOf I.r
        (readyDOf I.r (roleAfter I.rs.role I.ss) I.es I.ce I.ms I.qs I.sts)) := by
  obtain ⟨hphs, hdents, hdel, -, -, hflw, -, hdt⟩ := hrv
  have hpn : phsNext I.rs.phs I.h = I.rs.phs := phsNext_empty _ _ (Classical.not_not.mp hn)
  have hrole := roleS_drainOf (v := I.v) (qs := I.qs) (sts := I.sts) hout
  refine ⟨⟨?_, ?_, ?_, rfl, rfl, hflw, ?_, ?_⟩, ?_, hN.2⟩
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.drainOf]; rw [hpn]; exact hphs
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.drainOf]
    rw [hes, readyDurable_nil]; exact hdents
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.drainOf, readyDOf]
    rw [hdel, hce]; simp
  · exact hrole.symm
  · simp only [DrainIterB1.rs₂, AntSim.NodeView.drainOf, readyDurable, RaftState.next, hpn]
    rw [hphs]
  · have : (AntSim.accepted I.r).full = I.v.r.full := by
      simpa [AntSim.accepted, RState.full] using hfv
    simp only [AntSim.NodeView.drainOf]; rw [this]; exact hN.1

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The run's invariant at node `j`'s view** (B1's `drain_peekRecs`): the relation's facts at the
invariant's sent lists, past the caller's lower bounds (in B1's mask, the network's and node `j`'s),
and the view's full log certified (`raftFactsOwn`'s `logs`). -/
theorem drain_peekRecsB1 (h_vu : view_update.law (GF := GF)) (h_lo : nodeLive_over.law (GF := GF))
    (h_mask : runInMask.law AntSim.mskB1) (γ : AntNames) (j : Fin γ.R.N) (v : AntSim.NodeView)
    (net₀ : List Msg) (xnet₀ : List XMsg)
    (hrun : InScope γ.scope γ.mode ∧ ModeRun γ.scope γ.mode γ.R) (hb1 : DrainB1 γ.scope γ.mode) :
    inv antN (antInv (GF := GF) γ) ∗ sentLb γ net₀ ∗ xsentLb γ xnet₀ ∗ viewFrag γ j v ∗
        nodeLive γ j ⊢
      |={⊤}=> ⌜∃ (S : AntCheck.State) (net : List Msg) (xnet : List XMsg), net₀ <+: net ∧
          xnet₀ <+: xnet ∧ AntSim.InMask AntSim.mskB1 γ.R net xnet ∧ AntSim.NetOk γ.R S net ∧
          AntSim.NodeOk γ.R γ.dec S net j v⌝ ∗
        logRecs γ.raft.raftNames base0 v.r.full ∗ ⌜AntSim.LogIdx v.r.full⌝ ∗
        viewFrag γ j v ∗ nodeLive γ j := by
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
    imod h_vu (⊤ \ ↑antN) γ j V v v $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    rw [setV_self_s HVj]
    ihave #HF' := HF
    iunfold raftFactsOwn at HF'
    icases HF' with ⟨-, -, #Hlogs, -, -, -⟩
    have hmem : v.r.full ∈ G.logs := by rw [← HVj]; exact Hpure.2.2.2 j
    ihave ⟨#Hrv, %Hli⟩ := BigSepL.bigSepL_mem
      (Φ := fun l => iprop(logRecs γ.raft.raftNames base0 l ∗ ⌜AntSim.LogIdx l⌝)) hmem $$ Hlogs
    have hin := h_mask γ evs S V net xnet hrun.1 hrun.2 hb1 Hpure.1
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInv
      ileft
      iunfold antOpen
      iexists evs, S, V, net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro; exact Hpure
    imodintro
    iframe Hv Hl Hrv
    ipureintro
    have hA := Hpure.1.2.1
    exact ⟨⟨S, net, xnet, Hpre.2, Hxpre.2, hin, hA.2.2.1, by rw [← HVj]; exact hA.2.2.2.2 j⟩, Hli⟩
  · iexfalso
    iapply h_lo γ j
    iframe Hl Hover

end proof

end AntHarness
end EtcdGrove
end Perennial
