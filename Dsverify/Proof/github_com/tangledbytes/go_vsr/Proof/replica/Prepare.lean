/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Prepare.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onPrepare`: a backup accepts the next op of its view (`stepAccept`), queues the Prepare's Commit, sends its PrepareOK; a gap or a later view starts a state transfer.
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
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.InitiateStateTransfer
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Exec

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


set_option hygiene false in
/-- The end of `onPrepare`'s accepting path: the replica with the accepted entry. -/
macro "prep_close" : tactic => `(tactic| (
  have hpkq : ∀ k e, replica.pokOk (GF := GF) γ n tcp vn r k e = replica.pokOk γ n tcp v r k e := by
    intro k e; rw [hvn]; rfl
  have hdvq : ∀ w e, replica.dvOk (GF := GF) γ vn w e = replica.dvOk γ v w e := by
    intro w e; rw [hvn]; rfl
  have hgsq : replica.gstOk (GF := GF) n vn r = replica.gstOk n v r := by rw [hvn]; rfl
  have hrepq : replica.repOf vn (lg ++ [⟨ev.Request'.Op', uint.nat ev.Request'.ClientID',
      uint.nat ev.Request'.ID'⟩]) =
      { replica.repOf v lg with log := lg ++ [⟨ev.Request'.Op', uint.nat ev.Request'.ClientID',
        uint.nat ev.Request'.ID'⟩] } := by rw [hvn]; rfl
  have hmvq : replica.mineView vn = replica.mineView v := by rw [hvn]; rfl
  have hnpq : replica.IsNormalPrimary n vn r ↔ replica.IsNormalPrimary n v r := by rw [hvn]; rfl
  ihave #Hlog2 : log.ownLogs sl' DFrac.discard
      (lg ++ [(⟨ev.Request'.Op', uint.nat ev.Request'.ClientID', uint.nat ev.Request'.ID'⟩ :
        Entry)]) $$ []
  · iExactEq Hlog'; rfl
  ihave #Hcf2 : VsrGhost.fact γ (.committedBy cw
      ((lg ++ [(⟨ev.Request'.Op', uint.nat ev.Request'.ClientID', uint.nat ev.Request'.ID'⟩ :
        Entry)]).take (uint.nat v.state'.CommitNumber'))) $$ []
  · rw [List.take_append_of_le_length Hcommit.1]; iexact Hcfact
  iapply HΦ
  iexists vn
  iframe Hr
  iexists lg ++ [⟨ev.Request'.Op', uint.nat ev.Request'.ClientID', uint.nat ev.Request'.ID'⟩],
    mine, cw, mw, me, C, F, P, ms, replica.recReq tbl ev.Request'.ClientID' ev.Request'.ID',
    pk, sv, dv, vst, cst, n
  simp only [hpkq, hdvq, hgsq, hrepq, hmvq, hnpq]
  rw [hvnV, hvnO, hvnC, hvnI, hvnM, hvnL, hvnN, hvnLg, hvnS, hvnTm, hvnSv, hvnIn]
  rw [hvnT]
  iFrameNamed
  iframe Hlog2 Hcf2
  ihave #Htres2 := replica.tblOk_recReq γ tbl ev.Request'.ClientID' ev.Request'.ID' $$ Htres
  iframe Htres2
  ipureintro
  refine ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, by rw [hop1]; simp,
    ⟨by simp; have := Hcommit.1; omega, Hcommit.2⟩,
    ⟨Hmine.1, Hmine.2.1.trans (List.prefix_append _ _), Hmine.2.2⟩,
    replica.covers_recReq_mono _ _ _ _ Htmine, fun h => absurd h.2 hnotp⟩))

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

set_option maxHeartbeats 4000000 in
/-- A valid Prepare from an `addrOk` source. -/
theorem replica.wp_onPrepare (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (ev : events.Prepare) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗ network.addrOk tcp src ∗
        VsrGhost.fact γ (.msg (.prepare (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
          (uint.nat ev.CommitNum') ⟨ev.Request'.Op', uint.nat ev.Request'.ClientID',
            uint.nat ev.Request'.ID'⟩ (uint.nat ev.ReplicaID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onPrepare")) (Val #src)) (Val #ev))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, #Ha, #Hpf⟩
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply (H.wp_String_ptr from_ptr (DFrac.own 1) src) $$ [«from»] as «from»
  · iexact «from»
  wp_log
  wp_if_destruct
  rotate_left
  · wp_log
    close_own
  have Hst0 := Hif
  wp_apply (replica.wp_potentialPrimary _ _ _ n (by omega)) $$ [Hr] as Hr
  · iframe Hr Hms; ipureintro; exact Hmslen
  wp_if_destruct
  · wp_log
    close_own
  have Hnprim := Hif
  ihave %Hmlen0 := ownSlice_len $$ Hms
  have hn63 : n < 2 ^ 63 := by rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen0).2
  have hnotp : primary n (uint.nat v.state'.ViewNumber') ≠ r := by
    rw [replica.primary_word _ _ hn63, ← Hid.1]; intro h; apply Hnprim; word
  irename ev => Hev
  wp_if_destruct
  · -- an old view
    wp_log
    close_own
  wp_if_destruct
  · -- a later view
    lag_st
  have Hveq : ev.ViewNum' = v.state'.ViewNumber' := by
    rename_i h1 h2; apply BitVec.eq_of_toNat_eq; word
  wp_if_destruct
  rotate_left
  · -- not the next op
    lag_st
  have Hnext := Hif
  -- the model: the log's bound, the step (stepAccept)
  have hr3 : r < n := Hid.2
  ihave #Hnil : ([∗list] f ∈ ([] : List Fact), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_pure_rep' γ n r _ [] (lg.length ≤ 6 * 2 ^ 28)
    (fun s hs hsn hrp _ => by
      have := VsrModel.repLog_length_le s hs r (show r < s.n from hsn ▸ hr3); rw [hrp] at this; exact this)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, %Hblen⟩
  have hop1 : uint.nat (v.state'.OpNum' + W64 1) = lg.length + 1 := by
    have : uint.nat v.state'.OpNum' ≤ 6 * 2 ^ 28 := by omega
    rw [← Hopnum]; word
  have hopk : uint.nat ev.OpNum' = lg.length + 1 := by rw [← Hnext]; exact hop1
  ihave #Hfs : ([∗list] f ∈ [Fact.msg (.prepare (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
      (uint.nat ev.CommitNum') ⟨ev.Request'.Op', uint.nat ev.Request'.ClientID',
        uint.nat ev.Request'.ID'⟩ (uint.nat ev.ReplicaID'))], VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hpf
  imod VsrReplica.ghost_step' γ n r (replica.repOf v lg)
    { replica.repOf v lg with log := lg ++ [(⟨ev.Request'.Op', uint.nat ev.Request'.ClientID',
        uint.nat ev.Request'.ID'⟩ : Entry)] } _
    [Fact.msg (.prepareOK (uint.nat v.state'.ViewNumber') (uint.nat ev.OpNum')
        (uint.nat v.state'.ID')),
     Fact.msg (.commit (uint.nat ev.ViewNum') (uint.nat ev.CommitNum') (uint.nat (W64 0)))]
    (fun s => stepAccept s r ⟨ev.Request'.Op', uint.nat ev.Request'.ClientID',
        uint.nat ev.Request'.ID'⟩)
    (fun s hs hsn hrp hf => by
      have hn : (s.reps r).status = .normal := by
        rw [hrp]; simp [replica.repOf, replica.statusOf, Hst0]
      have hp : primary s.n (s.reps r).view ≠ r := by rw [hrp, hsn]; exact hnotp
      have hm := hf _ (List.mem_singleton_self _)
      have hm' : MsgValid s (.prepare (s.reps r).view ((s.reps r).log.length + 1)
          (uint.nat ev.CommitNum') ⟨ev.Request'.Op', uint.nat ev.Request'.ClientID',
            uint.nat ev.Request'.ID'⟩ (uint.nat ev.ReplicaID')) := by
        rw [hrp]
        show MsgValid s (.prepare (uint.nat v.state'.ViewNumber') (lg.length + 1) _ _ _)
        rw [← Hveq, ← hopk]; exact hm
      obtain ⟨hI, hL⟩ := VsrModel.stepAccept_inv s r _ _ _ hs (show r < s.n from hsn ▸ hr3) hn hp hm'
      obtain ⟨f1, f2, f3, f4⟩ := VsrReplica.stepAccept_frame s r
        ⟨ev.Request'.Op', uint.nat ev.Request'.ClientID', uint.nat ev.Request'.ID'⟩
      rw [hrp] at f1
      refine ⟨hI, hL, f1, f2, f3, f4, ?_⟩
      intro f hf'
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hf'
      rcases hf' with rfl | rfl
      · have := VsrModel.prepareOK_own _ hI r (lg.length + 1) (show r < s.n from hsn ▸ hr3)
          (by rw [f1]; left; simp [replica.repOf, replica.statusOf, Hst0])
          (by rw [f1]; simp only [replica.repOf, List.length_append, List.length_singleton]; omega)
        rw [f1] at this
        rw [hopk, Hid.1]
        exact this
      · exact VsrModel.holds_mono hL (.msg _)
          (VsrModel.commit_of_prepare s (uint.nat ev.ViewNum') (uint.nat ev.OpNum')
            (uint.nat ev.CommitNum') (uint.nat ev.ReplicaID') (uint.nat (W64 0)) _ hm))
    $$ Hsize Hsys Hrep Hfs with ⟨Hrep, Hfs'⟩
  icases Hfs' with ⟨#Hpok, #Hcmt, -⟩
  -- the log's append, through the field's points-to
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hr
  iStructNamedPrefix Hr "R"
  ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ Rstate
  iStructNamedPrefix Rstate "S"
  wp_apply (H.wp_Add _ v.state'.Logs' DFrac.discard lg _ DFrac.valid_discard)
    $$ [SLogs Hcap] as ⟨%sl', SLogs, #Hlog', Hcap⟩
  · iframe SLogs Hcap Hlog
  obtain ⟨vn, hvn⟩ : ∃ vn : replica.Replica, vn = { v with state' := { v.state' with
      OpNum' := v.state'.OpNum' + W64 1, Logs' := sl' } } := ⟨_, rfl⟩
  ihave Rstate := typedPointsto_combine _ vn.state' _ Hnn2 $$
    [SID SViewNumber SCommitNumber SOpNum SClientTable SClusterMembers SLogs SStatus]
  · rw [hvn]; simp only [TypedPointsto.typedPointstoDef]; iframe
  ihave Hr := typedPointsto_combine _ vn _ Hnn $$
    [Rstate Rnetwork Rtime Rlogger Rsrvhandler Rheartbeattimeout Rinternal]
  · simp only [TypedPointsto.typedPointstoDef]; iframe; rw [hvn]; iframe
  have hvnV : vn.state'.ViewNumber' = v.state'.ViewNumber' := by rw [hvn]
  have hvnO : vn.state'.OpNum' = v.state'.OpNum' + W64 1 := by rw [hvn]
  have hvnC : vn.state'.CommitNumber' = v.state'.CommitNumber' := by rw [hvn]
  have hvnI : vn.state'.ID' = v.state'.ID' := by rw [hvn]
  have hvnT : vn.state'.ClientTable' = v.state'.ClientTable' := by rw [hvn]
  have hvnM : vn.state'.ClusterMembers' = v.state'.ClusterMembers' := by rw [hvn]
  have hvnL : vn.state'.Logs' = sl' := by rw [hvn]
  have hvnN : vn.network' = v.network' := by rw [hvn]
  have hvnLg : vn.logger' = v.logger' := by rw [hvn]
  have hvnS : vn.state'.Status' = v.state'.Status' := by rw [hvn]
  have hvnTm : vn.time' = v.time' := by rw [hvn]
  have hvnSv : vn.srvhandler' = v.srvhandler' := by rw [hvn]
  have hvnIn : vn.internal' = v.internal' := by rw [hvn]
  irename Hlogger => Hlogger0
  ihave #Hlogger : log.slog.isLogger vn.logger' $$ []
  · rw [hvnLg]; iexact Hlogger0
  wp_apply (replica.wp_recordRequest rp vn tbl ev.Request'.ClientID' ev.Request'.ID') $$ [Hr Htbl]
    as ⟨Hr, Htbl⟩
  · iframe Hr; rw [hvnT]; iexact Htbl
  -- the Prepare's Commit, queued
  ipersist «$v1»
  have hvnQ : vn.internal'.sq' = v.internal'.sq' := by rw [hvn]
  rw [hvnQ]
  wp_apply (H.wp_Push events.NetworkEvent.ty (replica.sqElem γ tcp) v.internal'.sq'
    ⟨src, «$v1_ptr»⟩) $$ []
  · iframe Hsq
    unfold replica.sqElem
    ileft
    iexists (.commit (uint.nat ev.ViewNum') (uint.nat ev.CommitNum') (uint.nat (W64 0)))
    iframe Hcmt Ha
    isplitl []
    · unfold events.isEvent
      simp only [events.typeOf, events.payloadOf]
      iexists _
      iframe «$v1»
      iexists _
      ipureintro
      refine ⟨rfl, ?_⟩
      simp
    · unfold events.evCap; itrivial
  -- the PrepareOK to the primary
  ihave #Hpok2 : VsrGhost.fact γ (.msg (.prepareOK (uint.nat vn.state'.ViewNumber')
      (uint.nat ev.OpNum') (uint.nat vn.state'.ID'))) $$ []
  · rw [hvnV, hvnI]; iexact Hpok
  wp_apply (replica.wp_sendPrepareOKToPrimary H rp vn γ tcp C F src ev.OpNum')
    $$ [Hr Hsender] as %err ⟨Hr, Hsender, #Herr⟩
  · iframe Hr Hsender Ha Hpok2
    unfold replica.sendCtx
    iexists me
    iframe HisTCP Hprotos Hcodec Hkit Hsys
    ipureintro; rw [hvnN]; exact Hnet
  cases err with
  | nil =>
    wp_auto
    wp_log
    prep_close
  | ok ii =>
    wp_auto
    wp_apply (H.wp_String_ptr from_ptr (DFrac.own 1) src) $$ [«from»] as «from»
    · iexact «from»
    wp_log
    prep_close

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
