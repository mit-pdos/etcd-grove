/-
Lean-first (no Rocq counterpart). #33 S4: **`Cluster.drain`'s loop head** (`Cluster__drain.lean`):
`nodeOwn`'s `loop` phase opened into the `RawNode` (what `HasReady` and `Ready` take) and the rest
(`loopRest`: the storage, raft's per-node ghost state, the Go fields, the cause cell, the view, the
right to report, the sent list's lower bound); and the loop's exit (`drain_exit`: `HasReady` false,
the view moved to the node's state by `Quiet.noReady`, the node drained, its `by` kept).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The loop head but the `RawNode`** (`nodeOwn`'s `loop` phase at the client's record `rs`). -/
def loopRest (γ : AntNames) (j : Fin 3) (n : Loc) (v : AntSim.NodeView) (net₀ : List Msg)
    (rs : RNState) : IProp GF :=
  iprop(∃ (ms si cl : Loc) (applied : w64),
    n.[H.node, go!"storage"] ↦□ ms ∗
    nodeStor si ms (HardStateM.mk v.ps.term v.ps.vote v.ps.commit) ∗
    ⌜rs.storage = interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩⌝ ∗
    nodeRaft γ j rs ∗
    n.[H.node, go!"role"] ↦ roleStr (roleGo v.ps.role) ∗ n.[H.node, go!"term"] ↦ v.ps.term ∗
    n.[H.node, go!"vote"] ↦ v.ps.vote ∗ n.[H.node, go!"commit"] ↦ v.ps.commit ∗
    n.[H.node, go!"applied"] ↦ applied ∗ n.[H.node, go!"cause"] ↦ cl ∗
    viewFrag γ j v ∗ nodeLive γ j ∗ sentLb γ net₀ ∗ causeOwn γ j v cl ∗ ⌜ByOk v.byE⌝)

/-- **`nodeOwn`'s loop phase opened.** -/
theorem nodeOwn_loop_open (c : Loc) (γ : AntNames) (j : Fin 3) (n : Loc) (v : AntSim.NodeView)
    (net₀ : List Msg) (ps₁ : PState) :
    nodeOwn (GF := GF) c γ j n v (.loop net₀ ps₁) ⊢
      ∃ (rn : Loc) (rs : RNState) (ip : Nat),
        n.[H.node, go!"rn"] ↦□ rn ∗ rawNode γ.raft.raftNames rn (AntSim.nodeId j) rs ps₁ [] ip ∗
        ⌜RsView rs v ∧ AntSim.Reach (AntSim.nodeId j) net₀ v ps₁ ∧ ip = lcpLen v.ps.log ps₁.log⌝ ∗
        loopRest γ j n v net₀ rs := by
  unfold nodeOwn
  iintro ⟨%rn, %ms, %si, %rs, %ps, %qs, %ip, %cl, %applied, #Hrn, #Hms, Hbs, %Hsto, Hraw, Hnr,
    %Hrv, Hrole, Hterm, Hvote, Hcommit, Happ, Hcause, Hv, Hl, ⟨%Hph, #Hlb, Hco⟩⟩
  obtain ⟨rfl, hR, rfl, hip, hby⟩ := Hph
  iexists rn, rs, ip
  iframe Hrn Hraw
  isplitr
  · ipureintro; exact ⟨Hrv, hR, hip⟩
  iunfold loopRest
  iexists ms, si, cl, applied
  iframe Hms Hbs Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl Hlb Hco
  ipureintro; exact ⟨Hsto, hby⟩

/-- **The loop's exit** (`HasReady` false at the loop head): the view moved to the node's state
(`noReady_of`, `quiet_upd`), the node drained; the view's `by` kept. -/
theorem drain_exit (c : Loc) (γ : AntNames) (j : Fin 3) (n : Loc) (v : AntSim.NodeView)
    (net₀ : List Msg) (ps₁ : PState) (rn : Loc) (rs : RNState) (ip : Nat)
    (hrv : RsView rs v) (hR : AntSim.Reach (AntSim.nodeId j) net₀ v ps₁)
    (hP : PIdle rs ps₁) (hip : ip = ps₁.log.length) :
    inv antN (antInv (GF := GF) γ) ∗ n.[H.node, go!"rn"] ↦□ rn ∗
        rawNode γ.raft.raftNames rn (AntSim.nodeId j) rs ps₁ [] ip ∗ loopRest γ j n v net₀ rs ⊢
      |={⊤}=> nodeOwn c γ j n { v with ps := ps₁, qs := [] } .drained := by
  obtain ⟨hq, hI, hrv', ht, hv, hc, hr, hl⟩ := noReady_of hR hP hrv
  iintro ⟨#Hinv, #Hrn, Hraw, Hrest⟩
  iunfold loopRest at Hrest
  icases Hrest with ⟨%ms, %si, %cl, %applied, #Hms, Hbs, %Hsto, Hnr, Hrole, Hterm, Hvote, Hcommit,
    Happ, Hcause, Hv, Hl, #Hlb, Hco, -⟩
  imod quiet_upd γ j v { v with ps := ps₁, qs := [] } net₀ hq hl $$ [Hv Hl] with ⟨Hv, Hl⟩
  · iframe Hinv Hlb Hv Hl
  imodintro
  unfold nodeOwn
  iexists rn, ms, si, rs, ps₁, [], ip, cl, applied
  simp only [ht, hv, hc, hr]
  iframe Hrn Hms Hbs Hraw Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl
  isplitr
  · ipureintro; exact Hsto
  isplitr
  · ipureintro; exact hrv'
  isplitr
  · ipureintro; simp only [true_and]; exact ⟨hI, by rw [hip], hP⟩
  unfold causeOwn
  iexact Hco

/-! ## The next loop head's record -/

/-- **The record after `Ready`, the write's handshake and `Advance`** agrees with the view the
iteration's reports leave (`v₁`: the node at `pAccepted ps₁`, the committed entries handed out
delivered): `RsView` at the next loop head. -/
theorem rsView_next {id : w64} {rs : RNState} {v v₁ : AntSim.NodeView} {ps₁ : PState}
    {h : HardStateM} {es ce : List EntryM} {ms : List QMsg} {ss : Option (w64 × StateType)}
    {L : Option SnapLoan} {steps : List Pending} {W : DurMaps} {t : w64} {ca : Nat}
    (hrv : RsView rs v) (hce : v.ce = []) (hout : ReadyOut id rs ps₁ h es ce ms ss L)
    (hps : v₁.ps = pAccepted ps₁) (hdl : v₁.delivered = v.delivered ++ ce) (hce₁ : v₁.ce = []) :
    RsView (advRS
      { rs with delivered := rs.delivered ++ ce, unpersisted := [], steps := steps, outlb := 0,
                unst := false, phs := phsNext rs.phs h, psnap := false, slent := L,
                dur := readyDurable rs.dur (phsNext rs.phs h) L es,
                role := roleAfter rs.role ss, bw := W } t ca) v₁ := by
  obtain ⟨hra, hnext, hdur, -, -, -, -, -, hL⟩ := hout
  subst hL
  obtain ⟨-, -, -, hdel, -, -, -⟩ := hrv
  rw [advRS_none _ _ rfl]
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [hps, pAccepted]; exact hnext
  · simp only [hps, pAccepted]; exact hra
  · simp only [hps, pAccepted]; exact hdur
  · simp only [hdel, hce, hce₁, hdl, List.append_nil]

/-- **The next loop head, at the protocol level** (`Reach.advance`): the view `v₁` after the
iteration's reports (the node at `pAccepted ps₁`, its self-addressed messages queued, nothing left to
send or apply, the drain's `by` one of the harness's) reaches `Advance`'s end state `ps'`, and
`Advance`'s in-progress boundary (`min ip' (lcpLen …)`, `ip'` the log's end after `Ready`) is the
common prefix of the view's log and `ps'`'s. -/
theorem reach_next {id : w64} {net : List Msg} {v₁ : AntSim.NodeView} {ps₁ ps' : PState}
    {ip' ip'' : Nat} (hps : v₁.ps = pAccepted ps₁) (hpend : v₁.pend = []) (hce : v₁.ce = [])
    (hby : ByOk v₁.byE) (hadv : AdvanceEnd AntSim.cfgM3 id (pAccepted ps₁) v₁.qs ps')
    (hip' : ip' = ps₁.log.length)
    (hip'' : ip'' = min ip' (lcpLen (pAccepted ps₁).log ps'.log)) :
    AntSim.Reach id net v₁ ps' ∧ ip'' = lcpLen v₁.ps.log ps'.log := by
  refine ⟨.advance v₁ ps' hpend hce hby (by rw [hps]; exact hadv), ?_⟩
  rw [hip'', hip', hps]
  have := lcpLen_le_left (pAccepted ps₁).log ps'.log
  simp only [pAccepted] at this ⊢
  omega

/-- **`nodeOwn`'s loop phase closed** (`nodeOwn_loop_open`'s converse). -/
theorem nodeOwn_loop_close (c : Loc) (γ : AntNames) (j : Fin 3) (n : Loc) (v : AntSim.NodeView)
    (net₀ : List Msg) (ps₁ : PState) (rn : Loc) (rs : RNState) (ip : Nat)
    (hrv : RsView rs v) (hR : AntSim.Reach (AntSim.nodeId j) net₀ v ps₁)
    (hip : ip = lcpLen v.ps.log ps₁.log) :
    n.[H.node, go!"rn"] ↦□ rn ∗ rawNode (GF := GF) γ.raft.raftNames rn (AntSim.nodeId j) rs ps₁ [] ip ∗
        loopRest γ j n v net₀ rs ⊢
      nodeOwn c γ j n v (.loop net₀ ps₁) := by
  iintro ⟨#Hrn, Hraw, Hrest⟩
  iunfold loopRest at Hrest
  icases Hrest with ⟨%ms, %si, %cl, %applied, #Hms, Hbs, %Hsto, Hnr, Hrole, Hterm, Hvote, Hcommit,
    Happ, Hcause, Hv, Hl, #Hlb, Hco, %hby⟩
  unfold nodeOwn
  iexists rn, ms, si, rs, ps₁, [], ip, cl, applied
  iframe Hrn Hms Hbs Hraw Hnr Hrole Hterm Hvote Hcommit Happ Hcause Hv Hl
  isplitr
  · ipureintro; exact Hsto
  isplitr
  · ipureintro; exact hrv
  isplitr
  · ipureintro; exact ⟨rfl, hR, rfl, hip, hby⟩
  iframe Hlb Hco

end proof

end AntHarness
end EtcdGrove
end Perennial
