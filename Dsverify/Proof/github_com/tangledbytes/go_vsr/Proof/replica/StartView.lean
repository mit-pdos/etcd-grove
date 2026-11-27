/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/StartView.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onStartView`: a replica behind the view (or changing to it) installs the view's initial log (`stepStartView`; the StartView never reaches the view's primary: `startView_not_primary`), sends PrepareOKs of the uncommitted ops.
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
variable [package_sem : replica.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- A valid StartView, its log read-only with its capacity. -/
theorem replica.wp_onStartView (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (ev : events.StartView) (logs : List Entry) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗
        log.ownLogs ev.Logs' DFrac.discard logs ∗ ownSliceCap log.Log ev.Logs' (DFrac.own 1) ∗
        VsrGhost.fact γ (.msg (.startView (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
          (uint.nat ev.CommitNum') logs (uint.nat ev.ReplicaID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onStartView")) (Val #src)) (Val #ev))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, #Hlogs, Hcaps, #Hsvf⟩
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply (H.wp_String_ptr src_ptr (DFrac.own 1) src) $$ [src] as src
  · iexact src
  wp_log
  wp_if_destruct
  · -- an old view
    wp_log
    close_own
  wp_join (Q := fun b => iprop(⌜b = #(decide (ev.ViewNum' = v.state'.ViewNumber' ∧
      v.state'.Status' ≠ W64 1))⌝ ∗ rp ↦ v ∗ r_ptr ↦ rp)) at (If _ _ (Val #false))
      with [Hr r] as ⟨%hb, Hr, r⟩
  · wp_if_destruct
    · iframe
      ipureintro
      simp_all
    · iframe
      ipureintro
      simp_all
  subst hb
  wp_if_destruct
  · -- the view already started
    wp_log
    close_own
  rename_i Hlt
  have hr3 : r < n := Hid.2
  have hv : (replica.repOf v lg).view < uint.nat ev.ViewNum' ∨
      ((replica.repOf v lg).view = uint.nat ev.ViewNum' ∧
        (replica.repOf v lg).status = .viewChange) := by
    simp only [replica.repOf]
    by_cases heq : ev.ViewNum' = v.state'.ViewNumber'
    · right
      have h1 : v.state'.Status' = W64 1 :=
        Classical.byContradiction fun hne => Hif ⟨heq, hne⟩
      refine ⟨by rw [heq], ?_⟩
      simp [replica.statusOf, h1]
    · left
      have : uint.Z ev.ViewNum' ≠ uint.Z v.state'.ViewNumber' := fun h => heq (by word)
      word
  ihave #Hfs : ([∗list] f ∈ [Fact.msg (.startView (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
      (uint.nat ev.CommitNum') logs (uint.nat ev.ReplicaID')), Fact.committedBy mw mine],
      VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitl []
    · iexact Hsvf
    iapply (BI.BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitl []
    · iexact Hmcom
    iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_pure_rep' γ n r (replica.repOf v lg) _
    (uint.nat ev.OpNum' = logs.length ∧ uint.nat ev.CommitNum' ≤ logs.length ∧
      mine <+: logs ∧ primary n (uint.nat ev.ViewNum') ≠ r ∧ mw < uint.nat ev.ViewNum')
    (fun s hs hsn hrp hf => by
      have hm : MsgValid s (.startView (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
          (uint.nat ev.CommitNum') logs (uint.nat ev.ReplicaID')) :=
        hf (.msg (.startView (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
          (uint.nat ev.CommitNum') logs (uint.nat ev.ReplicaID'))) (by simp)
      have hmc : CommittedBy s mw mine := hf (.committedBy mw mine) (by simp)
      obtain ⟨hI, hk, hc, -⟩ := hm
      have hv' : (s.reps r).view < uint.nat ev.ViewNum' ∨
          ((s.reps r).view = uint.nat ev.ViewNum' ∧ (s.reps r).status = .viewChange) := by
        rw [hrp]; exact hv
      have hmwv : mw < uint.nat ev.ViewNum' := by
        have hmv := Hmine.2.2
        unfold replica.mineView at hmv
        split at hmv
        · rename_i hvc
          have := VsrReplica.lnv_lt_view s hs r (show r < s.n from hsn ▸ hr3) (by rw [hrp]; exact hvc)
          rw [hrp] at this
          simp only [replica.repOf] at this hv
          omega
        · rename_i hvc
          simp only [replica.repOf] at hv
          rcases hv with hv | ⟨-, hv⟩
          · omega
          · exact absurd hv hvc
      exact ⟨hk, by omega, VsrModel.startView_mine s (uint.nat ev.ViewNum') mw logs mine hs hI hmwv hmc,
        fun hp => VsrReplica.startView_not_primary s hs _ logs hI r (by rw [hsn]; exact hp) hv', hmwv⟩)
    $$ Hsize Hsys Hrep Hfs with ⟨Hrep, %Hpure⟩
  obtain ⟨Hk, Hc, Hml, Hnp, Hmwv⟩ := Hpure
  ihave #Hfs1 : ([∗list] f ∈ [Fact.msg (.startView (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
      (uint.nat ev.CommitNum') logs (uint.nat ev.ReplicaID'))], VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hsvf
  imod VsrReplica.ghost_step' γ n r (replica.repOf v lg)
    { replica.repOf v lg with view := uint.nat ev.ViewNum', status := .normal, log := logs } _
    [Fact.committedBy (uint.nat ev.ViewNum') (logs.take (uint.nat ev.CommitNum'))]
    (fun s => stepStartView s r (uint.nat ev.ViewNum') logs)
    (fun s hs hsn hrp hf => by
      have hm : MsgValid s (.startView (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
          (uint.nat ev.CommitNum') logs (uint.nat ev.ReplicaID')) :=
        hf (.msg (.startView (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
          (uint.nat ev.CommitNum') logs (uint.nat ev.ReplicaID'))) (by simp)
      have hv' : (s.reps r).view < uint.nat ev.ViewNum' ∨
          ((s.reps r).view = uint.nat ev.ViewNum' ∧ (s.reps r).status = .viewChange) := by
        rw [hrp]; exact hv
      obtain ⟨hinv, hle⟩ := stepStartView_inv s r (uint.nat ev.ViewNum') logs hs (show r < s.n from hsn ▸ hr3) hm.1 hv'
      obtain ⟨h1, h2, h3, h4⟩ := VsrReplica.stepStartView_frame s r (uint.nat ev.ViewNum') logs
      refine ⟨hinv, hle, by rw [h1, hrp], h2, h3, h4, ?_⟩
      intro f hfm
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hfm
      subst hfm
      exact holds_mono hle (.committedBy _ _)
        (committed_of_startView s _ _ _ _ logs hm))
    $$ Hsize Hsys Hrep Hfs1 with ⟨Hrep, Hfs'⟩
  icases Hfs' with ⟨#HcF, -⟩
  ihave #Hnil : ([∗list] f ∈ ([] : List Fact), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_pure_rep' γ n r _ [] (logs.length ≤ 6 * 2 ^ 28)
    (fun s hs hsn hrp _ => by
      have := VsrModel.repLog_length_le s hs r (show r < s.n from hsn ▸ hr3); rw [hrp] at this; exact this)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, %Hllen⟩
  unfold replica.ReplicaStatusNormal
  wp_auto
  obtain ⟨vf, hvf⟩ : ∃ vf : replica.Replica, vf = { v with state' := { v.state' with
      OpNum' := ev.OpNum', Logs' := ev.Logs', CommitNumber' := ev.CommitNum',
      ViewNumber' := ev.ViewNum', Status' := W64 0 } } := ⟨_, rfl⟩
  ihave Hr : rp ↦ vf $$ [Hr]
  · iExactEq Hr
    rw [hvf]
  have hvfV : vf.state'.ViewNumber' = ev.ViewNum' := by rw [hvf]
  have hvfI : vf.state'.ID' = v.state'.ID' := by rw [hvf]
  have hvfO : vf.state'.OpNum' = ev.OpNum' := by rw [hvf]
  have hvfT : vf.state'.ClientTable' = v.state'.ClientTable' := by rw [hvf]
  have hvfM : vf.state'.ClusterMembers' = v.state'.ClusterMembers' := by rw [hvf]
  have hvfN : vf.network' = v.network' := by rw [hvf]
  have hvfLg : vf.logger' = v.logger' := by rw [hvf]
  ihave HI : (∃ (i : w64) (tbl2 : GMap w64 replica.ClientTableData),
      "i" ∷ i_ptr ↦ i ∗ "Hr" ∷ rp ↦ vf ∗
      "Htbl" ∷ vf.state'.ClientTable' ↦$ tbl2 ∗
      "#Htres" ∷ ([∗map] c ↦ d ∈ tbl2, replica.tblOk γ c d) ∗
      "%Hi" ∷ ⌜uint.nat ev.CommitNum' + 1 ≤ uint.nat i ∧ uint.nat i ≤ logs.length + 1 ∧
        replica.Covers tbl2 mine⌝ : IProp GF) $$ [i Hr Htbl]
  · iexists _, tbl
    rw [hvfT]
    iframe i Hr Htbl Htres
    ipureintro
    refine ⟨by word, by word, Htmine⟩
  irename Hlogger => Hlogger0
  ihave #Hlogger : log.slog.isLogger vf.logger' $$ []
  · rw [hvfLg]; iexact Hlogger0
  irename Hms => Hms0
  ihave #Hms : vf.state'.ClusterMembers' ↦*□ ms $$ []
  · rw [hvfM]; iexact Hms0
  ihave %Hmlen := ownSlice_len $$ Hms
  have h3 : vf.state'.ClusterMembers'.len = W64 n := by
    rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).1
  have hn63 : n < 2 ^ 63 := by rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).2
  have hp3 : uint.nat (ev.ViewNum' % W64 n) < ms.length := by
    rw [Hmslen]; exact replica.umod_lt _ n hn63 (by omega)
  list_elem ms (uint.nat (ev.ViewNum' % W64 n)) as pm
  ihave #Hapm := BI.BigSepL.bigSepL_lookup Hpm_lookup $$ Haddrs
  wp_for HI
  wp_if_destruct
  · have hi1 : 1 ≤ uint.nat i := by omega
    have hil : uint.nat i ≤ logs.length := by rw [← Hk]; word
    list_elem logs (uint.nat i - 1) as ei
    have hlk : logs[sint.nat i - 1]? = some ei := by
      rw [show sint.nat i - 1 = uint.nat i - 1 by word]; exact Hei_lookup
    wp_method_call
    wp_auto
    wp_apply (H.wp_ClientIDAt ev.Logs' DFrac.discard logs i ei (by word) hlk) $$ [Hlogs]
    · iexact Hlogs
    iintro -
    wp_auto
    wp_method_call
    wp_auto
    wp_apply (H.wp_RequestIDAt ev.Logs' DFrac.discard logs i ei (by word) hlk) $$ [Hlogs]
    · iexact Hlogs
    iintro -
    wp_auto
    wp_apply (replica.wp_recordRequest rp vf tbl2 (W64 ei.cid) (W64 ei.req)) $$ [Hr Htbl]
      as ⟨Hr, Htbl⟩
    · iframe
    wp_log
    wp_apply (replica.wp_potentialPrimary _ _ _ n (by omega)) $$ [Hr] as Hr
    · iframe Hr Hms; ipureintro; exact Hmslen
    have hidx : 0 ≤ sint.Z (vf.state'.ViewNumber' % W64 n) ∧
        sint.Z (vf.state'.ViewNumber' % W64 n) < sint.Z vf.state'.ClusterMembers'.len := by
      have := replica.umod_lt ev.ViewNum' n hn63 (by omega)
      rw [h3, hvfV]; word
    rw [if_pos hidx]
    wp_apply (wp_load_slice_index _ (sint.Z (vf.state'.ViewNumber' % W64 n)) ms _ pm (by word))
      $$ [Hms]
    · iframe Hms; ipureintro
      rw [hvfV, show (sint.Z (ev.ViewNum' % W64 n)).toNat = uint.nat (ev.ViewNum' % W64 n) by word]
      exact Hpm_lookup
    iintro -
    wp_auto
    imod VsrReplica.ghost_fact' γ n r _ [] (.msg (.prepareOK (uint.nat ev.ViewNum') (uint.nat i) r))
      (fun s hs hsn hrp _ => by
        have := VsrModel.prepareOK_own s hs r (uint.nat i) (show r < s.n from hsn ▸ hr3) (by rw [hrp]; left; rfl)
          (by rw [hrp]; exact hil)
        rw [hrp] at this; exact this)
      $$ Hsize Hsys Hrep Hnil with ⟨Hrep, #Hpok⟩
    wp_apply (replica.wp_sendPrepareOKToPrimary H rp vf γ tcp C F pm i) $$ [Hr Hsender]
      as %err ⟨Hr, Hsender, #Herr⟩
    · iframe Hr Hsender Hapm
      isplitl []
      · unfold replica.sendCtx
        iexists me
        iframe HisTCP Hprotos Hcodec Hkit Hsys
        ipureintro; rw [hvfN]; exact Hnet
      rw [hvfV, hvfI, Hid.1]; iexact Hpok
    have hexi : ei ∈ logs := List.mem_of_getElem? Hei_lookup
    ihave ⟨%Hlb, -⟩ := log.ownLogs_bound _ _ _ $$ Hlogs
    obtain ⟨hcb, hqb⟩ := Hlb ei hexi
    ihave #Htres2 := replica.tblOk_recReq γ tbl2 (W64 ei.cid) (W64 ei.req) $$ Htres
    have Hcov : replica.Covers (replica.recReq tbl2 (W64 ei.cid) (W64 ei.req)) mine :=
      replica.covers_prefix _ (List.prefix_append _ _)
        (replica.covers_recReq tbl2 mine ei hcb hqb Hi.2.2)
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists (i + W64 1), _
      iframe Hr Htbl Htres2 i
      ipureintro
      refine ⟨by word, by word, Hcov⟩
    | ok ii =>
      wp_auto
      wp_apply (replica.wp_potentialPrimary _ _ _ n (by omega)) $$ [Hr] as Hr
      · iframe Hr Hms; ipureintro; exact Hmslen
      rw [if_pos hidx]
      icases ownSlice_elem_acc (sint.Z (vf.state'.ViewNumber' % W64 n)) pm _ _ ms (by word)
        (by rw [hvfV, show (sint.Z (ev.ViewNum' % W64 n)).toNat = uint.nat (ev.ViewNum' % W64 n)
          by word]; exact Hpm_lookup) $$ Hms with ⟨#Hel, -⟩
      wp_apply (H.wp_String_ptr _ _ pm) $$ [Hel] as -
      · iexact Hel
      wp_log
      wp_for_post
      iframe
      iexists (i + W64 1), _
      iframe Hr Htbl Htres2 i
      ipureintro
      refine ⟨by word, by word, Hcov⟩
  -- after the loop: the pending view-change entries of the view are dropped
  have hvfSV : vf.internal'.pendingStartViewChange' = v.internal'.pendingStartViewChange' := by
    rw [hvf]
  have hvfDV : vf.internal'.pendingDoViewChange' = v.internal'.pendingDoViewChange' := by
    rw [hvf]
  rw [hvfSV]
  wp_apply wp_mapDelete $$ Hsv as Hsv
  rw [hvfDV]
  wp_apply wp_mapDelete $$ Hdv as Hdv
  have hnorm : replica.statusOf vf.state'.Status' = .normal := by
    simp [replica.statusOf, hvf]
  have hnp : ¬ replica.IsNormalPrimary n vf r := by
    unfold replica.IsNormalPrimary; rw [hvfV]; exact fun h => Hnp h.2
  ihave Hsvs := replica.bigSepM_drop _ sv ev.ViewNum' $$ Hsvs
  ihave Hdvs := replica.bigSepM_drop _ dv ev.ViewNum' $$ Hdvs
  ihave Hdvs := BI.BigSepM.bigSepM_mono (M := GMap w64)
    (fun {k e'} _ => replica.dvOk_mono γ v vf k e' (by
      unfold replica.Live; intro hl
      rcases hl with hl | ⟨-, hs⟩
      · left; rw [hvfV] at hl
        simp only [replica.repOf] at hv
        omega
      · rw [hnorm] at hs; cases hs)) $$ Hdvs
  ihave Hpks := BI.BigSepM.bigSepM_mono (M := GMap w64)
    (fun {k e'} _ => replica.pokOk_notPrimary γ n tcp v vf r k e' hnp) $$ Hpks
  ihave Hgst : replica.gstOk n vf r $$ [Hgst]
  · unfold replica.gstOk
    icases Hgst with (%Hn | ⟨Ht, -⟩)
    · ileft; ipureintro; rw [hvf]; exact Hn
    · iright
      rw [show vf.internal'.getStateTimer' = v.internal'.getStateTimer' by rw [hvf]]
      iframe Ht
      ipureintro
      rw [hnorm, hvfV]
      exact ⟨by simp, Hnp⟩
  iapply HΦ
  iexists vf
  iframe Hr
  iexists logs, mine, uint.nat ev.ViewNum', mw, me, C, F, P, ms, tbl2, pk,
    GMap.delete ev.ViewNum' sv, GMap.delete ev.ViewNum' dv, vst, cst, n
  have hrepF : replica.repOf vf logs =
      { replica.repOf v lg with view := uint.nat ev.ViewNum', status := .normal, log := logs } := by
    simp [replica.repOf, hvfV, hnorm]; rw [hvf]
  have e2 : vf.time' = v.time' := by rw [hvf]
  have e5 : vf.srvhandler' = v.srvhandler' := by rw [hvf]
  have e6 : vf.internal'.sq' = v.internal'.sq' := by rw [hvf]
  have e7 : vf.internal'.pendingPOKs' = v.internal'.pendingPOKs' := by rw [hvf]
  have e10 : vf.internal'.viewChangeTimer' = v.internal'.viewChangeTimer' := by rw [hvf]
  have e11 : vf.internal'.commitTimer' = v.internal'.commitTimer' := by rw [hvf]
  have e12 : vf.internal'.lastExecutedOpNum' = v.internal'.lastExecutedOpNum' := by rw [hvf]
  have e13 : vf.state'.Logs' = ev.Logs' := by rw [hvf]
  have e14 : vf.state'.CommitNumber' = ev.CommitNum' := by rw [hvf]
  rw [hrepF, hvfM, hvfN, e2, hvfLg, e5, e6, e7, e10, e11, e12, e13, e14, hvfSV, hvfDV, hvfO,
    hvfV, hvfI]
  iFrameNamed
  iframe Hlogs Hcaps HcF
  ipureintro
  refine ⟨Hid, Hmslen, Hnet, Htime, by simp [replica.StatusOk, hvf], fun h => (by rw [hnorm] at h; cases h),
    Hk, ⟨Hc, Nat.le_refl _⟩, ⟨Hmine.1, Hml, ?_⟩, Hi.2.2, fun h => absurd h hnp⟩
  simp only [replica.mineView, hnorm, hvfV]
  simp only [reduceCtorEq, ↓reduceIte]
  omega

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
