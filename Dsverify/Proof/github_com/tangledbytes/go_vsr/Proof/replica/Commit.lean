/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Commit.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onCommit`: a backup in the Commit's view with enough ops executes up to the commit number (`committed_of_commit`, `ghost_lin` per op); otherwise a state transfer.
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


section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

set_option maxHeartbeats 2000000 in
/-- A valid Commit (received, or the internal Commit of a Prepare). -/
theorem replica.wp_onCommit (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (c : events.Commit) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗ network.addrOk tcp src ∗
        VsrGhost.fact γ (.msg (.commit (uint.nat c.ViewNum') (uint.nat c.CommitNum')
          (uint.nat c.ReplicaID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onCommit")) (Val #src)) (Val #c))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, #Ha, #Hcf⟩
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
  irename commit => Hev
  wp_if_destruct
  · -- an old view
    wp_log
    close_own
  wp_if_destruct
  · -- a later view
    lag_st
  have Hveq : c.ViewNum' = v.state'.ViewNumber' := by
    rename_i h1 h2; apply BitVec.eq_of_toNat_eq; word
  wp_if_destruct
  · -- ops missing
    lag_st
  -- the log up to the commit number is committed
  have hcl : uint.nat c.CommitNum' ≤ lg.length := by rw [← Hopnum]; word
  have hr3 : r < n := Hid.2
  ihave #Hcf1 : ([∗list] f ∈ [Fact.msg (.commit (uint.nat c.ViewNum') (uint.nat c.CommitNum')
      (uint.nat c.ReplicaID'))], VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hcf
  imod VsrReplica.ghost_fact' γ n r _ _
    (.committedBy (uint.nat v.state'.ViewNumber') (lg.take (uint.nat c.CommitNum')))
    (fun s hs hsn hrp hf => by
      have hm := hf _ (List.mem_singleton_self _)
      have h := VsrModel.committed_of_commit s hs r (uint.nat c.CommitNum') (uint.nat c.ReplicaID')
        (show r < s.n from hsn ▸ hr3) (by rw [hrp]; simp [replica.repOf, replica.statusOf, Hst0])
        (by rw [hrp]; show MsgValid s (.commit (uint.nat v.state'.ViewNumber') _ _)
            rw [← Hveq]; exact hm)
        (by rw [hrp]; exact hcl)
      rw [hrp] at h; exact h)
    $$ Hsize Hsys Hrep Hcf1 with ⟨Hrep, #Hcom⟩
  ihave #Hnil : ([∗list] f ∈ ([] : List Fact), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_pure_rep' γ n r _ [] (lg.length ≤ 6 * 2 ^ 28)
    (fun s hs hsn hrp _ => by
      have := VsrModel.repLog_length_le s hs r (show r < s.n from hsn ▸ hr3); rw [hrp] at this; exact this)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, %Hblen⟩
  ihave ⟨%Hlb, -⟩ := log.ownLogs_bound _ _ _ $$ Hlog
  have hmw : mw ≤ uint.nat v.state'.ViewNumber' := by
    have := Hmine.2.2; simpa [replica.mineView, replica.statusOf, Hst0] using this
  have hmine_take : mine = lg.take (uint.nat v.internal'.lastExecutedOpNum') := by
    rw [← Hmine.1]; exact VsrReplica.prefix_eq_take Hmine.2.1
  subst hmine_take
  ihave HI : (∃ (i cn le : w64) (tbl' : GMap w64 replica.ClientTableData) (cwI mwI : Nat),
      "i" ∷ i_ptr ↦ i ∗
      "Hr" ∷ rp ↦ replica.withExec v cn le ∗
      "Htbl" ∷ v.state'.ClientTable' ↦$ tbl' ∗
      "Hstore" ∷ P (storeOf (lg.take (uint.nat le))) ∗
      "#Hlin" ∷ VsrGhost.fact γ (.linPrefix (lg.take (uint.nat le))) ∗
      "#Htres" ∷ ([∗map] k ↦ d ∈ tbl', replica.tblOk γ k d) ∗
      "#Hcf" ∷ VsrGhost.fact γ (.committedBy cwI (lg.take (uint.nat cn))) ∗
      "#Hmc" ∷ VsrGhost.fact γ (.committedBy mwI (lg.take (uint.nat le))) ∗
      "%Hle" ∷ ⌜uint.nat i = uint.nat le + 1 ∧ uint.nat le ≤ lg.length ∧
        uint.nat cn ≤ lg.length ∧ cwI ≤ uint.nat v.state'.ViewNumber' ∧
        mwI ≤ uint.nat v.state'.ViewNumber' ∧
        replica.Covers tbl' (lg.take (uint.nat le)) ∧
        (replica.IsNormalPrimary n v r → replica.Covers tbl' lg)⌝ : IProp GF)
      $$ [i Hr Htbl Hstore]
  · iexists _, v.state'.CommitNumber', v.internal'.lastExecutedOpNum', tbl, cw, mw
    iframe i Htbl Hstore Hmlin Htres Hcfact Hmcom
    isplitl [Hr]
    · iExactEq Hr; rfl
    ipureintro
    have : uint.nat v.internal'.lastExecutedOpNum' ≤ lg.length := by
      have h1 := Hmine.1; rw [List.length_take] at h1; omega
    refine ⟨?_, this, Hcommit.1, Hcommit.2, hmw, Htmine, Htlog⟩
    word
  wp_for HI
  wp_if_destruct
  · -- execute op i
    obtain ⟨Hi, Hlel, Hcnl, Hcw, Hmw, Hcov1, Hcov2⟩ := Hle
    have hile : uint.nat i ≤ uint.nat c.CommitNum' := by word
    have hi1 : 1 ≤ uint.nat i := by omega
    have hlt : uint.nat le < lg.length := by omega
    list_elem lg (uint.nat le) as ex
    have hlk : lg[sint.nat i - 1]? = some ex := by
      rw [show sint.nat i - 1 = uint.nat le by word]; exact Hex_lookup
    wp_method_call
    wp_auto
    wp_apply (H.wp_OpAt _ DFrac.discard lg i ex (by word) hlk) $$ [Hlog]
    · iexact Hlog
    iintro -
    wp_log
    wp_method_call
    wp_auto
    wp_apply (H.wp_OpAt _ DFrac.discard lg i ex (by word) hlk) $$ [Hlog]
    · iexact Hlog
    iintro -
    wp_auto
    wp_bind (App (Val #v.srvhandler') (Val #ex.op))
    unfold examples.vsrkv.srvOk
    iapply Hsrv $$ Hstore
    inext
    iintro Hstore
    wp_auto
    ihave Hr : rp ↦ replica.withExec v i i $$ [Hr]
    · iExactEq Hr; rfl
    have hil : uint.nat i ≤ lg.length := by omega
    ihave #Hcom1 : ([∗list] f ∈ [Fact.committedBy (uint.nat v.state'.ViewNumber')
        (lg.take (uint.nat c.CommitNum'))], VsrGhost.fact γ f) $$ []
    · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hcom
    imod VsrReplica.ghost_fact' γ n r _ _
      (.committedBy (uint.nat v.state'.ViewNumber') (lg.take (uint.nat i)))
      (fun s hs hsn hrp hf => by
        have h := hf _ (List.mem_singleton_self _)
        exact VsrModel.committedBy_prefix s _ _ _ (VsrReplica.take_prefix_of_le lg hile) h)
      $$ Hsize Hsys Hrep Hcom1 with ⟨Hrep, #Hci⟩
    wp_method_call
    wp_auto
    wp_apply (H.wp_ClientIDAt _ DFrac.discard lg i ex (by word) hlk) $$ [Hlog]
    · iexact Hlog
    iintro -
    wp_auto
    wp_method_call
    wp_auto
    wp_apply (H.wp_RequestIDAt _ DFrac.discard lg i ex (by word) hlk) $$ [Hlog]
    · iexact Hlog
    iintro -
    wp_auto_lc 1
    have hle_op : uint.nat le < uint.nat c.CommitNum' := by omega
    have hml : lg.take (uint.nat le) <+: lg.take (uint.nat c.CommitNum') :=
      VsrReplica.take_prefix_of_le lg (by omega)
    have hlen_m : (lg.take (uint.nat le)).length = uint.nat le := by
      rw [List.length_take]; omega
    have hex' : (lg.take (uint.nat c.CommitNum'))[(lg.take (uint.nat le)).length]? = some ex := by
      rw [hlen_m, List.getElem?_take, if_pos hle_op]; exact Hex_lookup
    obtain ⟨hout, htk⟩ := VsrReplica.outOf_lin hml ex hex'
    rw [hlen_m] at hout htk
    imod VsrReplica.ghost_lin' γ (lg.take (uint.nat c.CommitNum')) (lg.take (uint.nat le))
      (uint.nat le + 1) ex (by rw [hlen_m]) hml (by simpa [hlen_m] using hex')
      (uint.nat v.state'.ViewNumber') (uint.nat v.state'.ViewNumber')
      $$ Hlc1 Hsys HregI Hcom Hlin with ⟨#Hlin', #Hrep'⟩
    rw [hout, htk]
    wp_apply (replica.wp_recordResult rp _ tbl' (W64 ex.cid) (W64 ex.req)
      (handle (storeOf (lg.take (uint.nat le))) ex.op).2) $$ [Hr Htbl] as ⟨Hr, Htbl⟩
    · iframe Hr; iExactEq Htbl; rfl
    have hexb : ex ∈ lg := List.mem_of_getElem? Hex_lookup
    obtain ⟨hcb, hqb⟩ := Hlb ex hexb
    ihave #Htres' := replica.tblOk_recRes γ tbl' (W64 ex.cid) (W64 ex.req)
      (handle (storeOf (lg.take (uint.nat le))) ex.op).2 (uint.nat v.state'.ViewNumber')
      $$ [Htres Hrep']
    · iframe Htres
      rw [show uint.nat (W64 ex.req) = ex.req by word, show uint.nat (W64 ex.cid) = ex.cid by word]
      iexact Hrep'
    have htki : lg.take (uint.nat i) = lg.take (uint.nat le) ++ [ex] := by
      rw [Hi]; exact VsrReplica.take_succ_eq lg _ ex Hex_lookup
    wp_for_post
    iframe
    iexists (i + W64 1), i, i, _, uint.nat v.state'.ViewNumber', uint.nat v.state'.ViewNumber'
    rw [htki, VsrReplica.storeOf_append_one]
    iframe Hr Htbl Hstore Hlin' Htres' Hci i
    ipureintro
    refine ⟨by word, by omega, by omega, Nat.le_refl _, Nat.le_refl _,
      replica.covers_recRes tbl' _ ex _ hcb hqb Hcov1,
      fun h => replica.covers_recRes_mono _ _ _ _ _ (Hcov2 h)⟩
  · -- the end of the loop
    obtain ⟨Hi, Hlel, Hcnl, Hcw, Hmw, Hcov1, Hcov2⟩ := Hle
    ihave Hrep : VsrGhost.repOwn γ r (replica.repOf (replica.withExec v cn le) lg) $$ [Hrep]
    · iExactEq Hrep; rfl
    ihave Hgst : replica.gstOk n (replica.withExec v cn le) r $$ [Hgst]
    · iExactEq Hgst; rfl
    ihave Hpks : ([∗map] k ↦ e ∈ pk, replica.pokOk γ n tcp (replica.withExec v cn le) r k e)
      $$ [Hpks]
    · iExactEq Hpks; rfl
    ihave Hdvs : ([∗map] w ↦ e ∈ dv, replica.dvOk γ (replica.withExec v cn le) w e) $$ [Hdvs]
    · iExactEq Hdvs; rfl
    iapply HΦ
    iexists replica.withExec v cn le
    iframe Hr
    iexists lg, lg.take (uint.nat le), cwI, mwI, me, C, F, P, ms, tbl', pk, sv, dv, vst, cst, n
    iFrameNamed
    simp only [replica.withExec]
    iframe Hcf Hlin Hmc
    ipureintro
    refine ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, ⟨Hcnl, Hcw⟩,
      ⟨by rw [List.length_take]; omega, List.take_prefix _ _, ?_⟩, Hcov1, Hcov2⟩
    simpa [replica.mineView, replica.statusOf, Hst0] using Hmw

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
