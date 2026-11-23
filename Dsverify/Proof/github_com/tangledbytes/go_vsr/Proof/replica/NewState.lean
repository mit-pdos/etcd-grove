/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/NewState.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onNewState`: a replica in state transfer appends a NewState of its view that extends its log (`stepNewState`), normal again.
(Stub: the spec, for parallel proving; `sorry` until proved.)
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.assert
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.ViewHelpers

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- A valid NewState, its log read-only. -/
theorem replica.wp_onNewState (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (ev : events.NewState) (logs : List Entry) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗
        log.ownLogs ev.Logs' DFrac.discard logs ∗
        VsrGhost.fact γ (.msg (.newState (uint.nat ev.ViewNum') logs (uint.nat ev.CommitNum')
          (uint.nat ev.OpNum') (uint.nat ev.ReplicaID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onNewState")) (Val #src)) (Val #ev))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, #Hlogs, #Hnsf⟩
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply (H.wp_String_ptr src_ptr (DFrac.own 1) src) $$ [src] as src
  · iexact src
  wp_log
  wp_if_destruct
  rotate_left
  · -- not in state transfer
    wp_log
    close_own
  wp_join (Q := fun b => iprop(⌜b = #(decide (ev.ViewNum' ≠ v.state'.ViewNumber' ∨
      uint.Z ev.OpNum' < uint.Z (W64 logs.length) ∨
      ev.OpNum' - W64 logs.length ≠ v.state'.OpNum'))⌝ ∗ rp ↦ v ∗ r_ptr ↦ rp ∗ ev_ptr ↦ ev))
      at (If (If _ (Val #true) _) (Val #true) _)
      with [Hr r ev] as ⟨%hb, Hr, r, ev⟩
  · wp_if_destruct
    · wp_method_call
      wp_auto
      wp_apply (H.wp_Len ev.Logs' DFrac.discard logs) $$ [Hlogs]
      · iexact Hlogs
      iintro -
      wp_auto
      wp_if_destruct
      · iframe
        ipureintro
        simp_all
      · wp_method_call
        wp_auto
        wp_apply (H.wp_Len ev.Logs' DFrac.discard logs) $$ [Hlogs]
        · iexact Hlogs
        iintro -
        wp_auto
        iframe
        ipureintro
        simp_all
        have : ¬ (BitVec.toNat ev.OpNum' < logs.length % 18446744073709551616) := by omega
        simp [this]
    · iframe
      ipureintro
      simp_all
  subst hb
  wp_if_destruct
  · -- does not extend the log
    wp_log
    close_own
  rename_i Hst3
  have hr3 : r < n := Hid.2
  have hev : ev.ViewNum' = v.state'.ViewNumber' := by
    apply Classical.byContradiction; intro h; exact Hif (Or.inl h)
  have hle : ¬ uint.Z ev.OpNum' < uint.Z (W64 logs.length) := fun h => Hif (Or.inr (Or.inl h))
  have hsub : ev.OpNum' - W64 logs.length = v.state'.OpNum' := by
    apply Classical.byContradiction; intro h; exact Hif (Or.inr (Or.inr h))
  ihave ⟨%Hlb, -⟩ := log.ownLogs_bound _ _ _ $$ Hlogs
  ihave #Hfs0 : ([∗list] f ∈ [Fact.msg (.newState (uint.nat ev.ViewNum') logs (uint.nat ev.CommitNum')
      (uint.nat ev.OpNum') (uint.nat ev.ReplicaID'))], VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hnsf
  imod VsrReplica.ghost_pure' γ _ (logs.length ≤ 6 * 2 ^ 28)
    (fun s hs hf => by
      have hm : MsgValid s (.newState (uint.nat ev.ViewNum') logs (uint.nat ev.CommitNum')
          (uint.nat ev.OpNum') (uint.nat ev.ReplicaID')) :=
        hf (.msg (.newState (uint.nat ev.ViewNum') logs (uint.nat ev.CommitNum')
          (uint.nat ev.OpNum') (uint.nat ev.ReplicaID'))) (by simp)
      obtain ⟨L, hL, hkL, hlen, -⟩ := hm
      have := VsrModel.vlog_length_le s hs _ L hL
      omega)
    $$ Hsys Hfs0 with %Hlogsb
  have hk : uint.nat ev.OpNum' = lg.length + logs.length := by
    rw [← Hopnum, ← hsub]
    have : uint.Z (W64 logs.length) = logs.length := by word
    word
  have hstST : (replica.repOf v lg).status = .stateTransfer := by
    simp [replica.repOf, replica.statusOf, Hst3]
  ihave #Hfs1 : ([∗list] f ∈ [Fact.msg (.newState (uint.nat ev.ViewNum') logs (uint.nat ev.CommitNum')
      (uint.nat ev.OpNum') (uint.nat ev.ReplicaID'))], VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hnsf
  imod VsrReplica.ghost_step' γ n r (replica.repOf v lg)
    { replica.repOf v lg with status := .normal, log := lg ++ logs } _ []
    (fun s => stepNewState s r logs)
    (fun s hs hsn hrp hf => by
      have hm : MsgValid s (.newState (uint.nat ev.ViewNum') logs (uint.nat ev.CommitNum')
          (uint.nat ev.OpNum') (uint.nat ev.ReplicaID')) :=
        hf (.msg (.newState (uint.nat ev.ViewNum') logs (uint.nat ev.CommitNum')
          (uint.nat ev.OpNum') (uint.nat ev.ReplicaID'))) (by simp)
      have hview : (s.reps r).view = uint.nat ev.ViewNum' := by
        rw [hrp, hev]; rfl
      have hm' : MsgValid s (.newState (s.reps r).view logs (uint.nat ev.CommitNum')
          (uint.nat ev.OpNum') (uint.nat ev.ReplicaID')) := by rw [hview]; exact hm
      obtain ⟨hinv, hle'⟩ := stepNewState_inv s r logs _ _ _ hs (show r < s.n from hsn ▸ hr3) (by rw [hrp]; exact hstST) hm'
        (by rw [hrp]; exact hk)
      obtain ⟨h1, h2, h3, h4⟩ := VsrReplica.stepNewState_frame s r logs
      refine ⟨hinv, hle', by rw [h1, hrp]; rfl, h2, h3, h4, by simp⟩)
    $$ Hsize Hsys Hrep Hfs1 with ⟨Hrep, -⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hr with ⟨Hr, %Hnn⟩
  iStructNamed Hr
  icases typedPointsto_not_null_dup _ _ _ $$ state with ⟨state, %Hnn2⟩
  iStructNamed state
  wp_apply (H.wp_Merge _ v.state'.Logs' DFrac.discard lg ev.Logs' DFrac.discard logs
    DFrac.valid_discard) $$ [Logs Hcap]
    as ⟨%sl', Logs, #Hlog', Hcap', -⟩
  · iframe Logs Hlog Hcap Hlogs
  obtain ⟨st1, hst1⟩ : ∃ st1 : replica.VSRState, st1 = replica.VSRState.mk v.state'.ID'
      ev.ViewNum' v.state'.CommitNumber' ev.OpNum' v.state'.ClientTable' v.state'.ClusterMembers'
      sl' v.state'.Status' := ⟨_, rfl⟩
  ihave state := typedPointsto_combine _ st1 (DFrac.own 1) Hnn2 $$ [ID ViewNumber CommitNumber OpNum ClientTable ClusterMembers Logs Status]
  · subst hst1; simp only [TypedPointsto.typedPointstoDef, named]; iframe
  obtain ⟨v1, hv1⟩ : ∃ v1 : replica.Replica, v1 = { v with state' := st1 } := ⟨_, rfl⟩
  ihave Hr := typedPointsto_combine _ v1 (DFrac.own 1) Hnn $$ [state network time logger srvhandler heartbeattimeout internal]
  · subst hv1; simp only [TypedPointsto.typedPointstoDef, named]; iframe
  unfold replica.ReplicaStatusNormal
  wp_auto
  obtain ⟨vf, hvf⟩ : ∃ vf : replica.Replica, vf = { v1 with
      state' := { v1.state' with Status' := W64 0 },
      internal' := { v1.internal' with getStateTimer' := null } } := ⟨_, rfl⟩
  ihave Hr : rp ↦ vf $$ [Hr]
  · iExactEq Hr; rw [hvf]
  subst hv1 hst1
  have hnorm : replica.statusOf vf.state'.Status' = .normal := by
    simp [replica.statusOf, hvf]
  have hvfV : vf.state'.ViewNumber' = v.state'.ViewNumber' := by rw [hvf]; exact hev
  have hnp : ¬ replica.IsNormalPrimary n vf r := by
    unfold replica.IsNormalPrimary; rw [hvfV]
    intro h
    have : replica.statusOf v.state'.Status' = .stateTransfer := by
      simp [replica.statusOf, Hst3]
    exact Hst this h.2
  ihave Hdvs := BI.BigSepM.bigSepM_mono (M := GMap w64)
    (fun {k e'} _ => replica.dvOk_mono γ v vf k e' (by
      unfold replica.Live; intro hl
      rcases hl with hl | ⟨-, hs⟩
      · left; rw [hvfV] at hl; exact hl
      · rw [hnorm] at hs; cases hs)) $$ Hdvs
  ihave Hpks := BI.BigSepM.bigSepM_mono (M := GMap w64)
    (fun {k e'} _ => replica.pokOk_notPrimary γ n tcp v vf r k e' hnp) $$ Hpks
  ihave Hgst : replica.gstOk n vf r $$ []
  · unfold replica.gstOk; ileft; ipureintro; rw [hvf]
  iapply HΦ
  iexists vf
  iframe Hr
  iexists lg ++ logs, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, n
  have hrepF : replica.repOf vf (lg ++ logs) =
      { replica.repOf v lg with status := .normal, log := lg ++ logs } := by
    simp [replica.repOf, hvfV, hnorm]; rw [hvf]
  have e1 : vf.state'.ClusterMembers' = v.state'.ClusterMembers' := by rw [hvf]
  have e2 : vf.network' = v.network' := by rw [hvf]
  have e3 : vf.time' = v.time' := by rw [hvf]
  have e4 : vf.logger' = v.logger' := by rw [hvf]
  have e5 : vf.srvhandler' = v.srvhandler' := by rw [hvf]
  have e6 : vf.internal'.sq' = v.internal'.sq' := by rw [hvf]
  have e7 : vf.internal'.pendingPOKs' = v.internal'.pendingPOKs' := by rw [hvf]
  have e8 : vf.internal'.pendingStartViewChange' = v.internal'.pendingStartViewChange' := by
    rw [hvf]
  have e9 : vf.internal'.pendingDoViewChange' = v.internal'.pendingDoViewChange' := by rw [hvf]
  have e10 : vf.internal'.viewChangeTimer' = v.internal'.viewChangeTimer' := by rw [hvf]
  have e11 : vf.internal'.commitTimer' = v.internal'.commitTimer' := by rw [hvf]
  have e12 : vf.internal'.lastExecutedOpNum' = v.internal'.lastExecutedOpNum' := by rw [hvf]
  have e13 : vf.state'.Logs' = sl' := by rw [hvf]
  have e14 : vf.state'.CommitNumber' = v.state'.CommitNumber' := by rw [hvf]
  have e15 : vf.state'.ID' = v.state'.ID' := by rw [hvf]
  have e16 : vf.state'.OpNum' = ev.OpNum' := by rw [hvf]
  have e17 : vf.state'.ClientTable' = v.state'.ClientTable' := by rw [hvf]
  have hmv : replica.mineView vf = replica.mineView v := by
    unfold replica.mineView
    rw [hnorm, hvfV]
    have : replica.statusOf v.state'.Status' ≠ .viewChange := by
      simp [replica.statusOf, Hst3]
    simp [this]
  rw [hrepF, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, hvfV,
    List.take_append_of_le_length Hcommit.1]
  iFrameNamed
  iframe Hlog' Hcap'
  ipureintro
  refine ⟨Hid, Hmslen, Hnet, Htime, by simp [replica.StatusOk, hvf],
    fun h => (by rw [hnorm] at h; cases h), by rw [hk]; simp, ⟨by simp; omega, Hcommit.2⟩,
    ⟨Hmine.1, Hmine.2.1.trans (List.prefix_append _ _), by rw [hmv]; exact Hmine.2.2⟩, Htmine,
    fun h => absurd h hnp⟩

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
