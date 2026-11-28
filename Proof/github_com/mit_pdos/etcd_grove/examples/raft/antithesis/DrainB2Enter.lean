/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E (the synchronous `node.drain`): **a
synchronous `Ready`'s facts under B2 at the loop head**:
- `drain_peekSimB2`: the run's relation at node `j` (`AntSimD`, the view `v` the run's), the sent lists
  extending the lower bounds, within the mask; the view's full log certified;
- `drain_bridgeB2`: the run with the driver modes off (`RunCfg.syncOff`, `shape_parD`'s bridge), where
  B1's bounds (`readyMsgNums`, `readNums_reach`, `causeNums_reach`, `readStates_reach`) apply;
- `node.drain.batchB2.stmt`: `node.drain.specB2` with batching on (synchronous storage), the case the
  main loop leaves to the batching step.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Shape
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1ReadNums
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1ReadStates
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MsgBounds

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The run with the driver modes off** (synchronous storage, unbatched, no `mem` queued, no split
write at node `n`): B1's relation at the run's checker state with node `n`'s undo stripped and the
commit indices lifted, the mask and the reach with the driver modes off. -/
theorem drain_bridgeB2 {msk : AntSim.SimMask} (hmsk : msk ≤ AntSim.mskB2) {R : AntSim.RunCfg}
    {dec : CCDec} {S : AntCheck.State} {V : Fin R.N → AntSim.NodeView} {net : List Msg}
    {xnet : List XMsg} {n : Fin R.N} {r₁ : RState} {Adm : List EntryM → CCState → Prop}
    (hin : AntSim.InMask msk R net xnet) (hs : AntSim.AntSimD R dec S V net xnet)
    (ha : R.md.async = false) (hb : R.drv.batch = false) (hm : (V n).mems = [])
    (hparts : (V n).parts = []) (hr : AntSim.ReachIn msk R dec Adm net xnet n (V n) r₁) :
    AntSim.InMask msk.b1Of R.syncOff net xnet ∧
      AntSim.NetOk R.syncOff (AntSim.liftC (AntSim.stripU n S)) net ∧
      AntSim.NodeOk R.syncOff dec (AntSim.liftC (AntSim.stripU n S)) net n (V n) ∧
      AntSim.ReachIn msk.b1Of R.syncOff dec Adm net xnet n (V n) r₁ := by
  obtain ⟨hsh, -, hn, -, hno⟩ := hs
  have hv := hno n
  have hu : (V n).undo ≠ none → (V n).made = false :=
    hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ha hb
  have hqn : S.queue[n.val]! = [] := by
    have hqi : AntSim.QueueIs S n (V n) := hv.2.2.2.2.1
    unfold AntSim.QueueIs at hqi; rw [hqi, hm]; rfl
  have hd : (V n).dur = AntSim.durOf (V n).r := by
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hparts
    rw [hm] at this; exact this
  have hqn' : (AntSim.stripU n S).queue[n.val]! = [] := hqn
  have hv' := AntSim.nodeOk_liftC (R := R.syncOff) hqn'
    (AntSim.nodeOkD_syncOff ha hb hm hparts hd hu (AntSim.nodeOkD_stripU hb hv))
  have hnet' : AntSim.NetOk R.syncOff (AntSim.liftC (AntSim.stripU n S)) net :=
    AntSim.netOkD_toB1L (R := R.syncOff) (S := AntSim.stripU n S) ha hsh.2.2.2.2.2.1
      (AntSim.netOkD_stripU n hn)
  exact ⟨hin.syncOff, hnet', hv', hr.syncOff⟩

/-- **B1's bounds on a synchronous `Ready` under B2**: its messages' numbers (and responses') within
`2 ^ 61` (`readyMsgNums`), its read states' indices (`readStates_reach`). -/
theorem drain_boundsB2 {msk : AntSim.SimMask} (hmsk : msk ≤ AntSim.mskB2) {R : AntSim.RunCfg}
    {dec : CCDec} {S : AntCheck.State} {V : Fin R.N → AntSim.NodeView} {net : List Msg}
    {xnet : List XMsg} {n : Fin R.N} {r₁ : RState} {rd : AntSim.ReadyD}
    {Adm : List EntryM → CCState → Prop}
    (hin : AntSim.InMask msk R net xnet) (hs : AntSim.AntSimD R dec S V net xnet)
    (ha : R.md.async = false) (hb : R.drv.batch = false) (hm : (V n).mems = [])
    (hparts : (V n).parts = []) (hr : AntSim.ReachIn msk R dec Adm net xnet n (V n) r₁)
    (hN : ViewNormal (V n)) (hsn : AntSim.StateNums (2 ^ 61) r₁.p) :
    (AntSim.ReadyOutP R n (V n) r₁ rd → ∀ q ∈ rd.msgs ++ rd.resp, AntSim.MsgNums (2 ^ 61) q) ∧
      ∀ st ∈ r₁.p.rd.states, uint.Z st.Index' < 2 ^ 61 := by
  obtain ⟨hin', hnet', hv', hr'⟩ := drain_bridgeB2 hmsk hin hs ha hb hm hparts hr
  have hm1 := AntSim.SimMask.b1Of_le hmsk
  refine ⟨fun hro => AntSim.readyMsgNums hm1 hin' hnet' hv' hr' hro hsn (causeNums_reach hnet' hv' hN)
    (AntSim.readNums_reach hm1 hin' hnet' hv' hr' hsn), ?_⟩
  exact AntSim.readStates_reach hm1 hin' hnet' hv' hr' hsn

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **(B2) The run's relation at node `j`, its view `v` the run's, and the view's log certified**
(`drain_peekRecsB2` with the whole relation `AntSimD` in place of its network and node parts). -/
theorem drain_peekSimB2 (h_vu : view_update.law (GF := GF)) (msk : AntSim.SimMask) (c : Loc)
    (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (v : AntSim.NodeView) (net₀ : List Msg)
    (xnet₀ : List XMsg)
    (hinm : ∀ S V net xnet, AntSim.AntSimD γ.R γ.dec S V net xnet → AntSim.InMask msk γ.R net xnet) :
    antClusterB2 (GF := GF) c γ ∗ sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗
        viewFrag γ.toAntNames j v ∗ runLive γ q ⊢
      |={⊤}=> ⌜∃ (S : AntCheck.State) (V : Fin γ.R.N → AntSim.NodeView) (net : List Msg)
          (xnet : List XMsg), net₀ <+: net ∧ xnet₀ <+: xnet ∧ AntSim.InMask msk γ.R net xnet ∧
          AntSim.AntSimD γ.R γ.dec S V net xnet ∧ V j = v⌝ ∗
        logRecs γ.raft.raftNames base0 v.r.full ∗ ⌜AntSim.LogIdx v.r.full⌝ ∗
        viewFrag γ.toAntNames j v ∗ runLive γ q := by
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
    imod h_vu (⊤ \ ↑antN) γ.toAntNames j V v v $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    rw [setV_self_s HVj]
    ihave #HF' := HF
    iunfold raftFactsOwn at HF'
    icases HF' with ⟨-, -, #Hlogs, -, -, -⟩
    have hmem : v.r.full ∈ G.logs := by rw [← HVj]; exact Hpure.2.2.2 j
    ihave ⟨#Hrv, %Hli⟩ := BigSepL.bigSepL_mem
      (Φ := fun l => iprop(logRecs γ.raft.raftNames base0 l ∗ ⌜AntSim.LogIdx l⌝)) hmem $$ Hlogs
    have hA := Hpure.1.2.1
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInvB2
      ileft
      iunfold antOpenB2
      iexists evs, S, V, net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro; exact Hpure
    imodintro
    iframe Hv Hl Hrv
    ipureintro
    exact ⟨⟨S, V, net, xnet, Hpre.2, Hxpre.2, hinm S V net xnet hA, hA, HVj⟩, Hli⟩
  · iexfalso
    iapply runLive_excl γ q
    iframe Hl Hover

variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- **`(*node).drain(by)` under B2, batching** (`node.drain.specB2` with synchronous storage and
batching on): the main loop's proof leaves this case to the batching step. -/
abbrev node.drain.batchB2.stmt : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (γ : AntNamesB2) (n : Loc) (j : Fin γ.R.N)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) (q : Qp),
  γ.mode.Async' = false → γ.mode.Batch' = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      antClusterB2 c γ ∗ nodeROB2 c γ n j ∗ nodeOwnB2 c γ j n v (.loop net₀ xnet₀ r₁ xs₁) ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜DrainB2 γ.scope γ.mode⌝ }}
    (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"drain")) (Val #v.byE))
  {{ (v' : AntSim.NodeView), RET #(); nodeOwnB2 c γ j n v' .drained ∗ nodeExitB2 c γ q ∗ threadTok ∗
      ⌜v'.byE = v.byE⌝ }}

end proof

end AntHarness
end EtcdGrove
end Perennial
