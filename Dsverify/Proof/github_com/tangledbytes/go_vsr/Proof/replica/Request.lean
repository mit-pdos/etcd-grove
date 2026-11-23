/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Request.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onRequest`: the primary appends a new request (`stepAppend`, dedup by the client table: `hnew`), records it, broadcasts Prepares, queues its own PrepareOK; a duplicate finished request is answered from the table.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Exec
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.log.Logs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.assert.Results

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


set_option hygiene false in
/-- The new request's path of `onRequest` (after the dedup checks, with `hfresh`: the client
table has no request of the client at or after this one): the model's `stepAppend`, the log's
append, `recordRequest`, the Prepares, the internal PrepareOK, the replica's state. -/
macro "request_tail" : tactic => `(tactic| (
  -- the model: the log's bound, the new entry, the step
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
  have hnew0 : ∀ e' ∈ lg, e'.cid = uint.nat req.ClientID' → e'.req < uint.nat req.ID' := by
    intro e' he' hc
    obtain ⟨d, hd, hle⟩ := Htlog hnp e' he'
    have hk : (W64 e'.cid : w64) = req.ClientID' := by rw [hc]; word
    rw [hk] at hd
    have := hfresh d hd
    omega
  ihave #Hfs : ([∗list] f ∈ [Fact.msg (.request (uint.nat req.ID') (uint.nat req.ClientID') req.Op'),
      Fact.committedBy cw (lg.take (uint.nat v.state'.CommitNumber'))], VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe Hreq
    iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2
    iexact Hcfact
  imod VsrReplica.ghost_step' γ n r (replica.repOf v lg)
    { replica.repOf v lg with log := lg ++ [(⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ : Entry)] } _
    [Fact.msg (.prepare (uint.nat v.state'.ViewNumber') (uint.nat (v.state'.OpNum' + W64 1))
        (uint.nat v.state'.CommitNumber') ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩
        (uint.nat v.state'.ID')),
     Fact.msg (.prepareOK (uint.nat v.state'.ViewNumber') (uint.nat (v.state'.OpNum' + W64 1))
        (uint.nat v.state'.ID'))]
    (fun s => stepAppend s r ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩)
    (fun s hs hsn hrp hf => by
      have hn : (s.reps r).status = .normal := by
        rw [hrp]; simp [replica.repOf, replica.statusOf, Hst0]
      have hp : primary s.n (s.reps r).view = r := by rw [hrp, hsn]; exact hnp.2
      have hreg : ∃ i, s.reg (uint.nat req.ClientID') (uint.nat req.ID') = some i ∧
          req.Op' = encOp i := by
        have := hf (.msg (.request (uint.nat req.ID') (uint.nat req.ClientID') req.Op'))
          (by simp)
        exact this
      have hcom : CommittedBy s cw (lg.take (uint.nat v.state'.CommitNumber')) := by
        have := hf (.committedBy cw (lg.take (uint.nat v.state'.CommitNumber'))) (by simp)
        exact this
      have hnew : ∀ e' ∈ (s.reps r).log, e'.cid = uint.nat req.ClientID' →
          e'.req < uint.nat req.ID' := by rw [hrp]; exact hnew0
      obtain ⟨hI, hL⟩ := VsrModel.stepAppend_inv s r ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ hs (show r < s.n from hsn ▸ hr3) hn hp hreg hnew
      obtain ⟨f1, f2, f3, f4⟩ := VsrReplica.stepAppend_frame s r
        ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩
      rw [hrp] at f1
      refine ⟨hI, hL, f1, f2, f3, f4, ?_⟩
      have hcom' : CommittedBy (stepAppend s r ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩)
          (uint.nat v.state'.ViewNumber')
          ((lg ++ [(⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ : Entry)]).take
            (uint.nat v.state'.CommitNumber')) := by
        rw [List.take_append_of_le_length Hcommit.1]
        exact VsrModel.holds_mono hL (.committedBy _ _)
          (VsrReplica.committedBy_mono s _ Hcommit.2 hcom)
      intro f hf'
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hf'
      rcases hf' with rfl | rfl
      · have := VsrModel.prepare_own _ hI r (uint.nat v.state'.CommitNumber')
          ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ (show r < s.n from hsn ▸ hr3)
          (by rw [f1]; simp [replica.repOf, replica.statusOf, Hst0])
          (by rw [f1]; show primary s.n _ = r; rw [hsn]; exact hnp.2) (by rw [f1]; simp)
          (by rw [f1]; simp only [replica.repOf, List.length_append, List.length_singleton]
              have := Hcommit.1; omega)
          (by rw [f1]; exact hcom')
        rw [f1] at this
        rw [hop1, Hid.1]
        simp only [replica.repOf, List.length_append, List.length_singleton] at this
        exact this
      · have := VsrModel.prepareOK_own _ hI r (lg.length + 1) (show r < s.n from hsn ▸ hr3)
          (by rw [f1]; left; simp [replica.repOf, replica.statusOf, Hst0])
          (by rw [f1]; simp only [replica.repOf, List.length_append, List.length_singleton]; omega)
        rw [f1] at this
        rw [hop1, Hid.1]
        exact this)
    $$ Hsize Hsys Hrep Hfs with ⟨Hrep, Hfs'⟩
  icases Hfs' with ⟨#Hprep, #Hpok, -⟩
  -- the log's append, through the field's points-to
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hr
  iStructNamedPrefix Hr "R"
  ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ Rstate
  iStructNamedPrefix Rstate "S"
  wp_apply (log.Logs.Add.wp_proof _ v.state'.Logs' DFrac.discard lg _ DFrac.valid_discard)
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
  irename Hlogger => Hlogger0
  ihave #Hlogger : log.slog.isLogger vn.logger' $$ []
  · rw [hvnLg]; iexact Hlogger0
  wp_apply (replica.wp_recordRequest rp vn tbl req.ClientID' req.ID') $$ [Hr Htbl]
    as ⟨Hr, Htbl⟩
  · iframe Hr; rw [hvnT]; iexact Htbl
  -- the Prepares
  ihave #Hprep2 : VsrGhost.fact γ (.msg (.prepare (uint.nat vn.state'.ViewNumber')
      (uint.nat vn.state'.OpNum') (uint.nat vn.state'.CommitNumber')
      ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ (uint.nat vn.state'.ID'))) $$ []
  · rw [hvnV, hvnO, hvnC, hvnI]; iexact Hprep
  ihave #Hms' : vn.state'.ClusterMembers' ↦*□ ms $$ []
  · rw [hvnM]; iexact Hms
  ihave %Hmlen := ownSlice_len $$ Hms'
  have h3 : vn.state'.ClusterMembers'.len = W64 n := by
    rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).1
  rename_i ui_ptr
  irename «from» => Hfrom
  ihave HJ : (∃ (j : w64) (mem : ipv4port.IPv4Port) (mi : w64),
      "i" ∷ i_ptr ↦ j ∗ "member" ∷ member_ptr ↦ mem ∗ "ui" ∷ ui_ptr ↦ mi ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j⌝ : IProp GF)
    $$ [-HΦ Hsender Hsv Hsvs Hdv Hdvs Hvct Hct Hgst Hpk Hpks Hstore r req Hfrom Hrep R_ S_
      Hcap Hr Htbl]
  · iexists _, _, _; iframe; ipureintro; word
  wp_for HJ
  rw [h3]
  wp_if_destruct
  · have hj3 : sint.nat j < ms.length := by
      have := (replica.len_of_slice _ _ Hmlen).2; rw [Hmslen] at this ⊢; word
    list_elem ms (sint.nat j) as m
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z vn.state'.ClusterMembers'.len by
      rw [h3]; word)]
    wp_apply (wp_load_slice_index _ (sint.Z j) ms _ m (by word)) $$ [Hms']
    · iframe Hms'; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hm_lookup
    iintro -
    wp_auto
    wp_if_destruct
    · wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; word
    wp_apply (ipv4port.IPv4Port.String_ptr.wp member_ptr (DFrac.own 1) m) $$ [member] as member
    · iexact member
    wp_log
    ihave #Ham := BI.BigSepL.bigSepL_lookup Hm_lookup $$ Haddrs
    wp_apply (replica.wp_sendPrepareToBackup H rp vn γ tcp C F m req)
      $$ [Hr Hsender] as %err ⟨Hr, Hsender, #Herr⟩
    · iframe Hr Hsender Ham Hprep2
      unfold replica.sendCtx
      iexists me
      iframe HisTCP Hprotos Hcodec Hkit Hsys
      ipureintro; rw [hvnN]; exact Hnet
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; word
    | ok ii =>
      wp_auto
      wp_apply (ipv4port.IPv4Port.String_ptr.wp member_ptr (DFrac.own 1) m) $$ [member] as member
      · iexact member
      wp_log
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; word
  wp_log
  -- the internal PrepareOK
  have hid3 : sint.nat vn.state'.ID' < ms.length := by
    have := Hid.1; have := Hid.2; rw [hvnI, Hmslen]; word
  list_elem ms (sint.nat vn.state'.ID') as mid
  rw [if_pos (show 0 ≤ sint.Z vn.state'.ID' ∧ sint.Z vn.state'.ID' < sint.Z vn.state'.ClusterMembers'.len by
    rw [h3]; have := Hid.1; have := Hid.2; rw [hvnI]; word)]
  wp_apply (wp_load_slice_index _ (sint.Z vn.state'.ID') ms _ mid (by word)) $$ [Hms']
  · iframe Hms'; ipureintro
    rw [show (sint.Z vn.state'.ID').toNat = sint.nat vn.state'.ID' by word]; exact Hmid_lookup
  iintro -
  wp_auto
  ipersist «$v1»
  have hvnQ : vn.internal'.sq' = v.internal'.sq' := by rw [hvn]
  rw [hvnQ]
  ihave #Hpok2 : VsrGhost.fact γ (.msg (.prepareOK (uint.nat vn.state'.ViewNumber')
      (uint.nat vn.state'.OpNum') (uint.nat vn.state'.ID'))) $$ []
  · rw [hvnV, hvnO, hvnI]; iexact Hpok
  wp_apply (queue.Queue.Push.wp events.NetworkEvent.ty (replica.sqElem γ tcp) v.internal'.sq'
    ⟨mid, «$v1_ptr»⟩) $$ []
  · iframe Hsq
    unfold replica.sqElem
    iright; ileft
    iexists _
    iframe «$v1» Hpok2 Ha
  -- the replica with the new entry
  have hpkq : ∀ k e, replica.pokOk (GF := GF) γ n tcp vn r k e = replica.pokOk γ n tcp v r k e := by
    intro k e; rw [hvn]; rfl
  have hdvq : ∀ w e, replica.dvOk (GF := GF) γ vn w e = replica.dvOk γ v w e := by
    intro w e; rw [hvn]; rfl
  have hgsq : replica.gstOk (GF := GF) n vn r = replica.gstOk n v r := by rw [hvn]; rfl
  have hrepq : replica.repOf vn (lg ++ [⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩]) =
      { replica.repOf v lg with
        log := lg ++ [⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩] } := by rw [hvn]; rfl
  have hmvq : replica.mineView vn = replica.mineView v := by rw [hvn]; rfl
  have hnpq : replica.IsNormalPrimary n vn r ↔ replica.IsNormalPrimary n v r := by rw [hvn]; rfl
  have hvnS : vn.state'.Status' = v.state'.Status' := by rw [hvn]
  have hvnTm : vn.time' = v.time' := by rw [hvn]
  have hvnSv : vn.srvhandler' = v.srvhandler' := by rw [hvn]
  have hvnIn : vn.internal' = v.internal' := by rw [hvn]
  ihave #Hlog2 : log.ownLogs sl' DFrac.discard
      (lg ++ [(⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ : Entry)]) $$ []
  · iExactEq Hlog'; rfl
  ihave #Hcf2 : VsrGhost.fact γ (.committedBy cw
      ((lg ++ [(⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ : Entry)]).take
        (uint.nat v.state'.CommitNumber'))) $$ []
  · rw [List.take_append_of_le_length Hcommit.1]; iexact Hcfact
  iapply HΦ
  iexists vn
  iframe Hr
  iexists lg ++ [⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩], mine, cw, mw, me, C, F, P,
    ms, replica.recReq tbl req.ClientID' req.ID', pk, sv, dv, vst, cst, n
  simp only [hpkq, hdvq, hgsq, hrepq, hmvq, hnpq]
  rw [hvnV, hvnO, hvnC, hvnI, hvnM, hvnL, hvnN, hvnLg, hvnS, hvnTm, hvnSv, hvnIn]
  rw [hvnT]
  iFrameNamed
  iframe Hlog2 Hcf2
  ihave #Htres2 := replica.tblOk_recReq γ tbl req.ClientID' req.ID' $$ Htres
  iframe Htres2
  ipureintro
  · have hcq : uint.nat req.ClientID' < 2 ^ 64 := by word
    have hqq : uint.nat req.ID' < 2 ^ 64 := by word
    have := replica.covers_recReq tbl lg ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩
      hcq hqq (Htlog hnp)
    simp only [show (W64 (uint.nat req.ClientID') : w64) = req.ClientID' by word,
      show (W64 (uint.nat req.ID') : w64) = req.ID' by word] at this
    refine ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, by rw [hop1]; simp, ⟨by simp; omega, Hcommit.2⟩,
      ⟨Hmine.1, Hmine.2.1.trans (List.prefix_append _ _), Hmine.2.2⟩,
      replica.covers_recReq_mono _ _ _ _ Htmine, fun _ => this⟩))

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

set_option maxHeartbeats 6000000 in
/-- A client request (valid), from a source `Send` may be given. -/
theorem replica.wp_onRequest (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (req : events.Request) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗ network.addrOk tcp src ∗
        VsrGhost.fact γ (.msg (.request (uint.nat req.ID') (uint.nat req.ClientID') req.Op')) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onRequest")) (Val #src)) (Val #req))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, #Ha, #Hreq⟩
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  ihave %Hmlen0 := ownSlice_len $$ Hms
  have hn63 : n < 2 ^ 63 := by rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen0).2
  wp_auto
  wp_apply (ipv4port.IPv4Port.String_ptr.wp from_ptr (DFrac.own 1) src) $$ [«from»] as «from»
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
  rotate_left
  · wp_apply (replica.wp_potentialPrimary _ _ _ n (by omega)) $$ [Hr] as Hr
    · iframe Hr Hms; ipureintro; exact Hmslen
    wp_log
    close_own
  have Hprim := Hif
  have hnp : replica.IsNormalPrimary n v r := by
    refine ⟨by simp [replica.statusOf, Hst0], ?_⟩
    rw [replica.primary_word _ _ hn63, ← Hprim]; exact Hid.1
  wp_apply wp_map_lookup2 $$ Htbl as Htbl
  wp_if_destruct
  · -- a known client
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp Hif
    simp only [hd, Option.getD_some]
    wp_log
    wp_if_destruct
    · -- the client's last request again
      have heq := Hif
      wp_log
      cases hfin : d.Finished'
      · -- in progress: dropped
        wp_auto
        close_own
      · -- finished: its recorded reply
        wp_auto
        wp_log
        ihave #Hd := BI.BigSepM.bigSepM_lookup hd $$ Htres
        ihave #Hd' : (∃ w : Nat, VsrGhost.fact γ (.msg (.reply (uint.nat d.RequestNumber')
            (uint.nat req.ClientID') w d.Result'))) $$ []
        · unfold replica.tblOk; rw [hfin, if_pos rfl]; iexact Hd
        icases Hd' with ⟨%w, #Hrf⟩
        ihave #Hrf1 : ([∗list] f ∈ [Fact.msg (.reply (uint.nat d.RequestNumber')
            (uint.nat req.ClientID') w d.Result')], VsrGhost.fact γ f) $$ []
        · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hrf
        imod VsrReplica.ghost_fact' γ n r _ _ (.msg (.reply (uint.nat req.ID')
            (uint.nat req.ClientID') (uint.nat v.state'.ViewNumber') d.Result'))
          (fun s hs hsn hrp hf => by
            have h := hf _ (List.mem_singleton_self _)
            rw [heq] at h; exact h)
          $$ Hsize Hsys Hrep Hrf1 with ⟨Hrep, #Hrf2⟩
        wp_apply (replica.wp_sendReplyToClient H rp v γ tcp C F src req.ClientID' req.ID'
            d.Result') $$ [Hr Hsender] as %err ⟨Hr, Hsender, #Herr⟩
        · iframe Hr Hsender Ha Hrf2
          unfold replica.sendCtx
          iexists me
          iframe HisTCP Hprotos Hcodec Hkit Hsys
          ipureintro; exact Hnet
        cases err with
        | nil =>
          wp_auto
          close_own
        | ok ii =>
          wp_auto
          wp_apply (ipv4port.IPv4Port.String_ptr.wp from_ptr (DFrac.own 1) src) $$ [«from»]
            as «from»
          · iexact «from»
          wp_log
          close_own
    · have hne := Hif
      wp_if_destruct
      · -- stale: dropped
        close_own
      · have hfresh : ∀ d', tbl !! req.ClientID' = some d' →
            uint.nat d'.RequestNumber' < uint.nat req.ID' := by
          intro d' hd'
          rw [hd] at hd'; cases hd'
          have hng := Hif
          have : d.RequestNumber' ≠ req.ID' := hne
          have : uint.nat d.RequestNumber' ≠ uint.nat req.ID' := fun h => this (by word)
          have : ¬ uint.nat req.ID' < uint.nat d.RequestNumber' := by
            intro h; apply hng; word
          omega
        request_tail
  · have hfresh : ∀ d, tbl !! req.ClientID' = some d →
        uint.nat d.RequestNumber' < uint.nat req.ID' := by
      intro d hd; simp [hd] at Hif
    request_tail

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
