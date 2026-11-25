/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/InitiateStateTransfer.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`initiateStateTransfer`: a normal (or transferring) replica that is not its view's primary enters state transfer (`stepEnterST`), sets its get-state timer `[view, op, target]`, sends a GetState; otherwise it drops the timer.
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

/-- Called by a replica that is not its view's primary unless it is changing views. -/
theorem replica.wp_initiateStateTransfer (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (v : replica.Replica) (N : Nat)
    (nv no : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.repInv γ r tcp v ∗ VsrGhost.fact γ (.size N) ∗
        ⌜replica.statusOf v.state'.Status' ≠ .viewChange →
          primary N (uint.nat v.state'.ViewNumber') ≠ r⌝ }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"initiateStateTransfer")) (Val #nv)) (Val #no))
    {{ RET #(); ∃ v' : replica.Replica, rp ↦ v' ∗ replica.repInv γ r tcp v' ∗
        ⌜v'.state'.ID' = v.state'.ID' ∧ v'.state'.ClusterMembers' = v.state'.ClusterMembers' ∧
          v'.logger' = v.logger' ∧ v'.network' = v.network' ∧
          v'.state'.ViewNumber' = v.state'.ViewNumber'⌝ }} := by
  wp_start as ⟨Hr, Hinv, #HsizeN, %Hpre⟩
  unfold replica.repInv
  iNamed Hinv
  imod VsrReplica.size_agree' γ N n $$ Hsys HsizeN Hsize with %HNn
  subst HNn
  wp_auto
  wp_log
  wp_join (Q := fun b => iprop(⌜b = #(decide (v.state'.Status' ≠ W64 0 ∧
      v.state'.Status' ≠ W64 3))⌝ ∗ rp ↦ v ∗ r_ptr ↦ rp))
      at (If _ _ (Val #false)) with [Hr r] as ⟨%hb, Hr, r⟩
  · wp_if_destruct
    · try wp_auto
      iframe
      ipureintro
      simp_all
    · iframe
      ipureintro
      simp_all
  subst hb
  wp_if_destruct
  · -- changing views: the timer is dropped
    have Hvc : v.state'.Status' ≠ W64 0 ∧ v.state'.Status' ≠ W64 3 := by simp_all
    obtain ⟨h0, h3⟩ := Hvc
    have hs1 : v.state'.Status' = W64 1 := by
      rcases Hstatus with h | h | h
      · exact absurd h h0
      · exact h
      · exact absurd h h3
    have hvc : replica.statusOf v.state'.Status' = .viewChange := by
      simp [replica.statusOf, hs1]
    obtain ⟨vf, hvf⟩ : ∃ vf : replica.Replica, vf = { v with
        internal' := { v.internal' with getStateTimer' := null } } := ⟨_, rfl⟩
    ihave Hr : rp ↦ vf $$ [Hr]
    · iExactEq Hr; rw [hvf]
    have hvfS : vf.state' = v.state' := by rw [hvf]
    have hvc' : replica.statusOf vf.state'.Status' = .viewChange := by rw [hvfS]; exact hvc
    have hnp : ¬ replica.IsNormalPrimary N vf r := by
      unfold replica.IsNormalPrimary; rw [hvc']; simp
    ihave Hdvs := BI.BigSepM.bigSepM_mono (M := GMap w64)
      (fun {k e'} _ => replica.dvOk_mono γ v vf k e' (by
        unfold replica.Live; rw [hvfS]; exact id)) $$ Hdvs
    ihave Hpks := BI.BigSepM.bigSepM_mono (M := GMap w64)
      (fun {k e'} _ => replica.pokOk_notPrimary γ N tcp v vf r k e' hnp) $$ Hpks
    ihave Hgst : replica.gstOk N vf r $$ []
    · unfold replica.gstOk; ileft; ipureintro; rw [hvf]
    iapply HΦ
    iexists vf
    iframe Hr
    isplitl
    · iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, N
      have hrepF : replica.repOf vf lg = replica.repOf v lg := by
        simp only [replica.repOf, hvfS]; rw [hvf]
      have e2 : vf.network' = v.network' := by rw [hvf]
      have e3 : vf.time' = v.time' := by rw [hvf]
      have e4 : vf.logger' = v.logger' := by rw [hvf]
      have e5 : vf.srvhandler' = v.srvhandler' := by rw [hvf]
      have e6 : vf.internal'.sq' = v.internal'.sq' := by rw [hvf]
      have e7 : vf.internal'.pendingPOKs' = v.internal'.pendingPOKs' := by rw [hvf]
      have e8 : vf.internal'.pendingStartViewChange' = v.internal'.pendingStartViewChange' := by
        rw [hvf]
      have e9 : vf.internal'.pendingDoViewChange' = v.internal'.pendingDoViewChange' := by
        rw [hvf]
      have e10 : vf.internal'.viewChangeTimer' = v.internal'.viewChangeTimer' := by rw [hvf]
      have e11 : vf.internal'.commitTimer' = v.internal'.commitTimer' := by rw [hvf]
      have e12 : vf.internal'.lastExecutedOpNum' = v.internal'.lastExecutedOpNum' := by rw [hvf]
      have hmv : replica.mineView vf = replica.mineView v := by
        unfold replica.mineView; rw [hvfS]; rw [hvf]
      rw [hrepF, hvfS, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hmv]
      iFrameNamed
      ipureintro
      exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine,
        fun h => absurd h hnp⟩
    ipureintro
    rw [hvfS]; rw [hvf]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hr3 : r < N := Hid.2
  have hnvc : replica.statusOf v.state'.Status' ≠ .viewChange := by
    intro h
    rcases Hstatus with h' | h' | h' <;> simp [replica.statusOf, h'] at h
    exact Hif ⟨by simp [h'], by simp [h']⟩
  have hprim := Hpre hnvc
  ihave #Hnil : ([∗list] f ∈ ([] : List Fact), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_step' γ N r (replica.repOf v lg)
    { replica.repOf v lg with status := .stateTransfer } [] []
    (fun s => stepEnterST s r)
    (fun s hs hsn hrp _ => by
      obtain ⟨hinv, hle⟩ := stepEnterST_inv s r hs (show r < s.n from hsn ▸ hr3) (by rw [hrp]; exact hnvc)
      obtain ⟨h1, h2, h3, h4⟩ := VsrReplica.stepEnterST_frame s r
      exact ⟨hinv, hle, by rw [h1, hrp], h2, h3, h4, by simp⟩)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, -⟩
  unfold replica.ReplicaStatusStateTransfer
  wp_auto
  obtain ⟨v1, hv1⟩ : ∃ v1 : replica.Replica, v1 = { v with
      state' := { v.state' with Status' := W64 3 } } := ⟨_, rfl⟩
  ihave Hr : rp ↦ v1 $$ [Hr]
  · iExactEq Hr; rw [hv1]
  have hv1M : v1.state'.ClusterMembers' = v.state'.ClusterMembers' := by rw [hv1]
  ihave #Hms1 : v1.state'.ClusterMembers' ↦*□ ms $$ []
  · rw [hv1M]; iexact Hms
  wp_apply (replica.wp_primaryForView rp v1 ms N (by omega)) $$ [Hr] as Hr
  · iframe Hr Hms1; ipureintro; exact Hmslen
  have hv1T : v1.internal'.getStateTimer' = v.internal'.getStateTimer' := by rw [hv1]
  wp_join iprop(∃ tgt : w64, targetReplica_ptr ↦ tgt ∗ ⌜uint.nat tgt < N⌝ ∗ rp ↦ v1 ∗
      r_ptr ↦ rp) at next
      with [targetReplica Hgst Hr r] as ⟨%tgt, targetReplica, %Htgt, Hr, r⟩
  · try wp_auto
    wp_if_destruct
    rotate_left
    · unfold replica.gstOk
      icases Hgst with (%Hn | ⟨⟨%a, Ht⟩, -⟩)
      · exfalso; rw [hv1T] at *; simp_all
      rw [hv1T]
      wp_apply H.wp_State $$ [Ht] as Ht
      · iexact Ht
      wp_auto
      wp_apply H.wp_Assert
      rcases a with ⟨arr⟩
      ihave %Halen := array_len _ _ _ _ $$ castedState
      obtain ⟨x, hx⟩ : ∃ x, arr[(2 : Int).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
      icases array_acc castedState_ptr 2 _ 3 ⟨arr⟩ x (by omega) hx $$ castedState with ⟨Hel, -⟩
      rw [show sint.Z (W64 2) = 2 from rfl]
      ihave %Hmlen := ownSlice_len $$ Hms1
      have h3 : v1.state'.ClusterMembers'.len = W64 N := by
        rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).1
      have hN63 : N < 2 ^ 63 := by rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).2
      wp_auto
      rw [h3, if_neg (by word)]
      wp_auto
      wp_join_done
      iexists _
      iframe
      ipureintro; exact replica.umod_lt _ N hN63 (by omega)
    · ihave %Hmlen := ownSlice_len $$ Hms1
      wp_join_done
      iexists _
      iframe
      ipureintro
      exact replica.umod_lt _ N (by rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).2)
        (by omega)
  have hv1Ti : v1.time' = v.time' := by rw [hv1]
  rw [hv1Ti]
  wp_apply (H.wp_NewTimer v.time' (W64 15000000000) Htime) as %tm Htm
  wp_apply (H.wp_SetState tm interface.nil _) $$ [Htm] as Htm
  · iexact Htm
  obtain ⟨vf, hvf⟩ : ∃ vf : replica.Replica, vf = { v1 with
      internal' := { v1.internal' with getStateTimer' := tm } } := ⟨_, rfl⟩
  ihave Hr : rp ↦ vf $$ [Hr]
  · iExactEq Hr; rw [hvf]
  subst hv1
  have hvfM : vf.state'.ClusterMembers' = v.state'.ClusterMembers' := by rw [hvf]
  have hvfI : vf.state'.ID' = v.state'.ID' := by rw [hvf]
  have hvfN : vf.network' = v.network' := by rw [hvf]
  have hvfLg : vf.logger' = v.logger' := by rw [hvf]
  have hvfV : vf.state'.ViewNumber' = v.state'.ViewNumber' := by rw [hvf]
  have hvfS : vf.state'.Status' = W64 3 := by rw [hvf]
  irename Hlogger => Hlogger0
  ihave #Hlogger : log.slog.isLogger vf.logger' $$ []
  · rw [hvfLg]; iexact Hlogger0
  irename Hms1 => Hms2
  ihave #Hmsf : vf.state'.ClusterMembers' ↦*□ ms $$ []
  · rw [hvfM]; iexact Hms
  ihave %Hmlen := ownSlice_len $$ Hmsf
  have h3 : vf.state'.ClusterMembers'.len = W64 N := by
    rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).1
  have ht3 : uint.nat tgt < ms.length := by rw [Hmslen]; exact Htgt
  list_elem ms (uint.nat tgt) as pm
  ihave #Hapm := BI.BigSepL.bigSepL_lookup Hpm_lookup $$ Haddrs
  have hidx : 0 ≤ sint.Z tgt ∧ sint.Z tgt < sint.Z v.state'.ClusterMembers'.len := by
    rw [← hvfM, h3]; word
  wp_auto
  rw [if_pos hidx]
  wp_apply (wp_load_slice_index _ (sint.Z tgt) ms _ pm (by word)) $$ [Hms]
  · iframe Hms; ipureintro
    rw [show (sint.Z tgt).toNat = uint.nat tgt by word]
    exact Hpm_lookup
  iintro -
  wp_auto
  imod VsrReplica.ghost_fact' γ N r _ []
    (.msg (.getState (uint.nat vf.state'.ViewNumber') (uint.nat vf.state'.OpNum')
      (uint.nat vf.state'.ID'))) (fun _ _ _ _ _ => trivial)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, #Hgsf⟩
  wp_apply (replica.wp_sendGetStateToReplica H rp vf γ tcp C F pm) $$ [Hr Hsender]
    as %err ⟨Hr, Hsender, #Herr⟩
  · iframe Hr Hsender Hapm Hgsf
    unfold replica.sendCtx
    iexists me
    iframe HisTCP Hprotos Hcodec Hkit Hsys
    ipureintro; rw [hvfN]; exact Hnet
  have hst : replica.statusOf vf.state'.Status' = .stateTransfer := by
    simp [replica.statusOf, hvfS]
  have hnp : ¬ replica.IsNormalPrimary N vf r := by
    unfold replica.IsNormalPrimary; rw [hst]; simp
  ihave Hdvs := BI.BigSepM.bigSepM_mono (M := GMap w64)
    (fun {k e'} _ => replica.dvOk_mono γ v vf k e' (by
      unfold replica.Live; intro hl
      rcases hl with hl | ⟨-, hs⟩
      · left; rw [hvfV] at hl; exact hl
      · rw [hst] at hs; cases hs)) $$ Hdvs
  ihave Hpks := BI.BigSepM.bigSepM_mono (M := GMap w64)
    (fun {k e'} _ => replica.pokOk_notPrimary γ N tcp v vf r k e' hnp) $$ Hpks
  ihave Hgst : replica.gstOk N vf r $$ [Htm]
  · unfold replica.gstOk
    iright
    isplitl
    · iexists (array.mk 3 [nv, no, tgt])
      rw [show vf.internal'.getStateTimer' = tm by rw [hvf]]
      iexact Htm
    ipureintro
    rw [hst, hvfV]
    exact ⟨by simp, hprim⟩
  have Hpost : vf.state'.ID' = v.state'.ID' ∧ vf.state'.ClusterMembers' = v.state'.ClusterMembers' ∧
      vf.logger' = v.logger' ∧ vf.network' = v.network' ∧
      vf.state'.ViewNumber' = v.state'.ViewNumber' := ⟨hvfI, hvfM, hvfLg, hvfN, hvfV⟩
  wp_join iprop(rp ↦ vf ∗ r_ptr ↦ rp ∗ targetReplica_ptr ↦ tgt) at (If _ _ _)
      with [Hr r targetReplica err] as ⟨Hr, r, targetReplica⟩
  · cases err with
    | nil =>
      wp_auto
      wp_join_done
    | ok ii =>
      wp_auto
      have hidx' : 0 ≤ sint.Z tgt ∧ sint.Z tgt < sint.Z vf.state'.ClusterMembers'.len := by
        rw [h3]; word
      rw [if_pos hidx']
      icases ownSlice_elem_acc (sint.Z tgt) pm _ _ ms (by word)
        (by rw [show (sint.Z tgt).toNat = uint.nat tgt by word]; exact Hpm_lookup) $$ Hmsf
        with ⟨#Hel, -⟩
      wp_apply (H.wp_String_ptr _ _ pm) $$ [Hel] as -
      · iexact Hel
      wp_log
      wp_join_done
  iapply HΦ
  iexists vf
  iframe Hr
  isplitl
  · iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, N
    have hrepF : replica.repOf vf lg = { replica.repOf v lg with status := .stateTransfer } := by
      simp only [replica.repOf, hst, hvfV]; rw [hvf]
    have e3 : vf.time' = v.time' := by rw [hvf]
    have e5 : vf.srvhandler' = v.srvhandler' := by rw [hvf]
    have e6 : vf.internal'.sq' = v.internal'.sq' := by rw [hvf]
    have e7 : vf.internal'.pendingPOKs' = v.internal'.pendingPOKs' := by rw [hvf]
    have e8 : vf.internal'.pendingStartViewChange' = v.internal'.pendingStartViewChange' := by
      rw [hvf]
    have e9 : vf.internal'.pendingDoViewChange' = v.internal'.pendingDoViewChange' := by
      rw [hvf]
    have e10 : vf.internal'.viewChangeTimer' = v.internal'.viewChangeTimer' := by rw [hvf]
    have e11 : vf.internal'.commitTimer' = v.internal'.commitTimer' := by rw [hvf]
    have e12 : vf.internal'.lastExecutedOpNum' = v.internal'.lastExecutedOpNum' := by rw [hvf]
    have e13 : vf.state'.Logs' = v.state'.Logs' := by rw [hvf]
    have e14 : vf.state'.CommitNumber' = v.state'.CommitNumber' := by rw [hvf]
    have e16 : vf.state'.OpNum' = v.state'.OpNum' := by rw [hvf]
    have e17 : vf.state'.ClientTable' = v.state'.ClientTable' := by rw [hvf]
    have hmv : replica.mineView vf = replica.mineView v := by
      unfold replica.mineView
      rw [hst, hvfV]
      simp [hnvc]
    rw [hrepF, hvfM, hvfN, e3, hvfLg, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e16, e17, hvfI,
      hvfV, hmv]
    iFrameNamed
    ipureintro
    refine ⟨Hid, Hmslen, Hnet, Htime, by simp [replica.StatusOk, hvfS],
      fun _ => hprim, Hopnum, Hcommit, Hmine, Htmine, fun h => absurd h hnp⟩
  ipureintro; exact Hpost

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
