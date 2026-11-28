/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **a synchronous `Ready`'s entries and
messages normal under B2** (`msgShape_core` over the run with the driver modes off, as
`antSim_quietP_in` reaches it): at a view with no `mem` queued and no split write, raft's full log and
each message's entries carry no configuration change. `node.parallel` reports the entries (`stateEv`)
and hands the requests to `sendEv` before any write, also when killed on the way.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Holds
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemView

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The `Ready`'s log and messages normal** (sync, unbatched, no `mem` queued, no split write). -/
theorem shape_parD {msk : AntSim.SimMask} (hmsk : msk ≤ AntSim.mskB2) {R : AntSim.RunCfg}
    {dec : CCDec} {S : AntCheck.State} {V : Fin R.N → AntSim.NodeView} {net : List Msg}
    {xnet : List XMsg} {n : Fin R.N} {r₁ : RState} {rd : AntSim.ReadyD}
    {Adm : List EntryM → CCState → Prop}
    (hin : AntSim.InMask msk R net xnet) (hs : AntSim.AntSimD R dec S V net xnet)
    (ha : R.md.async = false) (hb : R.drv.batch = false) (hm : (V n).mems = [])
    (hparts : (V n).parts = []) (hr : AntSim.ReachIn msk R dec Adm net xnet n (V n) r₁)
    (hrop : AntSim.ReadyOutP R n (V n) r₁ rd) (hfl : AntSim.EntsNormal (V n).r.full)
    (hcm : ∀ m, (V n).cause = some m → AntSim.EntsNormal m.entries) :
    AntSim.EntsNormal r₁.full ∧ ∀ q ∈ rd.msgs, AntSim.EntsNormal q.entries := by
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
  have hmsg := (hrop.2.2.2.2.2.2.2.2.1 ha).2
  have hnet' : AntSim.NetOk R.syncOff (AntSim.liftC (AntSim.stripU n S)) net :=
    AntSim.netOkD_toB1L (R := R.syncOff) (S := AntSim.stripU n S) ha hsh.2.2.2.2.2.1
      (AntSim.netOkD_stripU n hn)
  obtain ⟨hl, hq⟩ := AntSim.msgShape_core (AntSim.SimMask.b1Of_le hmsk) hin.syncOff hnet' hv'
    hr.syncOff hmsg hfl hcm
  exact ⟨hl, fun q h => (hq q h).2.2.1⟩

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **`shape_parD` in the run's invariant**: at a view with no `mem` queued and no split write,
reached from the sent lists' lower bounds, the `Ready`'s log and messages normal. -/
theorem drain_peekShapeB2 (h_vu : view_update.law (GF := GF)) (msk : AntSim.SimMask)
    (hmsk : msk ≤ AntSim.mskB2) (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp)
    (v : AntSim.NodeView) (r₁ : RState) (rd : AntSim.ReadyD) (net₀ : List Msg) (xnet₀ : List XMsg)
    {Adm : List EntryM → CCState → Prop}
    (hinm : ∀ S V net xnet, AntSim.AntSimD γ.R γ.dec S V net xnet → AntSim.InMask msk γ.R net xnet)
    (has : γ.R.md.async = false) (hbt : γ.R.drv.batch = false) (hm : v.mems = [])
    (hparts : v.parts = []) (hreach : AntSim.ReachIn msk γ.R γ.dec Adm net₀ xnet₀ j v r₁)
    (hrop : AntSim.ReadyOutP γ.R j v r₁ rd) (hfl : AntSim.EntsNormal v.r.full)
    (hcm : ∀ m, v.cause = some m → AntSim.EntsNormal m.entries) :
    antClusterB2 (GF := GF) c γ ∗ sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗
        viewFrag γ.toAntNames j v ∗ runLive γ q ⊢
      |={⊤}=> ⌜AntSim.EntsNormal r₁.full ∧ ∀ m ∈ rd.msgs, AntSim.EntsNormal m.entries⌝ ∗
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
    have hA := Hpure.1.2.1
    have hsh : AntSim.EntsNormal r₁.full ∧ ∀ m ∈ rd.msgs, AntSim.EntsNormal m.entries := by
      subst HVj
      exact shape_parD hmsk (hinm S V net xnet hA) hA has hbt hm hparts
        (hreach.mono Hpre.2 Hxpre.2) hrop hfl hcm
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInvB2
      ileft
      iunfold antOpenB2
      iexists evs, S, V, net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro; exact Hpure
    imodintro
    iframe Hv Hl
    ipureintro; exact hsh
  · iexfalso
    iapply runLive_excl γ q
    iframe Hl Hover

end proof

end AntHarness
end EtcdGrove
end Perennial
