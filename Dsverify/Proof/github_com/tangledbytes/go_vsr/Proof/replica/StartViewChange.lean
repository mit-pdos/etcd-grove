/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/StartViewChange.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onStartViewChange`: a later view starts a view change; a quorum of StartViewChanges of the replica's changing view sends its DoViewChange (`dvc_own`).
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
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.InitiateViewChange

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

/-- A StartViewChange (no validity needed). -/
theorem replica.wp_onStartViewChange (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (ev : events.StartViewChange) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onStartViewChange")) (Val #src)) (Val #ev))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as Hown
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply (H.wp_String_ptr src_ptr (DFrac.own 1) src) $$ [src] as src
  · iexact src
  wp_log
  wp_apply H.wp_Reset $$ [Hvct] as Hvct
  · iexact Hvct
  wp_if_destruct
  · -- an old view
    wp_log
    close_own
  rename_i Hge
  wp_join (Q := fun b => iprop(⌜b = #(decide (v.state'.Status' ≠ W64 1 ∧
      ev.ViewNum' = v.state'.ViewNumber'))⌝ ∗ rp ↦ v ∗ r_ptr ↦ rp ∗ ev_ptr ↦ ev))
      at (If _ _ (Val #false)) with [Hr r ev] as ⟨%hb, Hr, r, ev⟩
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
  · -- the view already started here
    wp_log
    close_own
  ihave Hinv : replica.repInv γ r tcp v $$ [-HΦ Hr r ev]
  · unfold replica.repInv
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, n
    iFrameNamed
    ipureintro
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩
  iclear Hms Haddrs HisTCP Hprotos Hsrv Hcodec Hkit Hsys HregI Hsq Hlog Hcfact Hmlin Hmcom Htres
  wp_join iprop(∃ v' : replica.Replica, rp ↦ v' ∗ replica.repInv γ r tcp v' ∗ r_ptr ↦ rp ∗
      ev_ptr ↦ ev ∗ log.slog.isLogger v'.logger' ∗
      ⌜v'.state'.ID' = v.state'.ID' ∧ v'.state'.ClusterMembers' = v.state'.ClusterMembers' ∧
        v'.logger' = v.logger' ∧ v'.network' = v.network' ∧
        v'.state'.ViewNumber' = ev.ViewNum' ∧ v'.state'.Status' = W64 1⌝)
      with [Hr Hinv r ev] as ⟨%v', Hr, Hinv, r, ev, #Hlogger', %Hv'⟩
  · wp_log
    wp_apply (replica.wp_initiateViewChange H rp γ r tcp v ev.ViewNum') $$ [Hr Hinv]
      as ⟨%v', Hr, Hinv, %Hv'⟩
    · iframe Hr Hinv; ipureintro; word
    isplitr
    · ipureintro; rfl
    iexists v'
    iframe Hr Hinv r ev
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hv'
    isplitl []
    · rw [h3]; iexact Hlogger
    ipureintro
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · iexists v
    iframe Hr Hinv r ev Hlogger
    ipureintro
    have hle : uint.Z ev.ViewNum' ≤ uint.Z v.state'.ViewNumber' := by word
    have heq : ev.ViewNum' = v.state'.ViewNumber' := by word
    refine ⟨rfl, rfl, rfl, rfl, heq.symm, ?_⟩
    exact Classical.byContradiction fun h => by simp_all
  iclear Hlogger Hlogger'
  obtain ⟨hI1, hI2, hI3, hI4, hV, hS⟩ := Hv'
  clear Hid Hmslen Hnet Htime Hstatus Hst Hopnum Hcommit Hmine Htmine Htlog
  unfold replica.repInv
  iNamed Hinv
  wp_if_destruct
  rotate_left
  · exfalso; simp_all
  wp_if_destruct
  rotate_left
  · exfalso; simp_all
  wp_apply wp_map_lookup2 $$ Hsv as Hsv
  wp_join iprop(∃ (sv' : GMap w64 replica.PendingStartViewChange)
      (e : replica.PendingStartViewChange),
      v'.internal'.pendingStartViewChange' ↦$ sv' ∗ ⌜sv' !! ev.ViewNum' = some e⌝ ∗
      ([∗map] _w ↦ e ∈ sv', replica.svOk e) ∗ rp ↦ v' ∗ r_ptr ↦ rp ∗ ev_ptr ↦ ev)
    with [Hsv Hsvs Hr r ev] as ⟨%sv', %e, Hsv, %Hse, Hsvs, Hr, r, ev⟩
  · obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp Hif
    iexists sv, e
    iframe Hsv Hsvs Hr r ev
    ipureintro; exact he
  · have hnone : sv !! ev.ViewNum' = none := by simpa using Hif
    wp_apply (wp_map_make1 (K := w64) (V := Unit)) as %m Hm
    wp_apply wp_mapInsert $$ Hsv as Hsv
    wp_join_done
    iexists _, _
    iframe Hsv Hr r ev
    isplitr
    · ipureintro; exact GMap.lookup_insert _ _ _
    iapply (BigSepM.bigSepM_insert hnone).2
    iframe Hsvs
    unfold replica.svOk
    iexists ∅
    iframe Hm
  ihave ⟨He, Hsvs⟩ := (BigSepM.bigSepM_delete Hse).1 $$ Hsvs
  ihave He : iprop(∃ rs : GMap w64 Unit, e.Responses' ↦$ rs) $$ [He]
  · unfold replica.svOk; iexact He
  icases He with ⟨%rs, Hrs⟩
  wp_apply wp_map_lookup1 $$ Hsv as Hsv
  simp only [Hse, Option.getD_some]
  wp_apply wp_mapInsert $$ Hrs as Hrs
  wp_apply wp_map_lookup1 $$ Hsv as Hsv
  simp only [Hse, Option.getD_some]
  wp_apply wp_map_len_lt $$ Hrs as ⟨Hrs, %Hsz⟩
  ihave Hsvs := (BigSepM.bigSepM_delete (M := GMap w64)
    (Φ := fun _ e => replica.svOk e) Hse).2 $$ [Hrs Hsvs]
  · iframe Hsvs
    unfold replica.svOk
    iexists _
    iexact Hrs
  ihave %Hmlen := ownSlice_len $$ Hms
  have h3 : v'.state'.ClusterMembers'.len = W64 n := by
    rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).1
  rw [h3]
  wp_if_destruct
  rotate_left
  · -- no majority yet
    iapply HΦ
    iexists v'
    iframe Hr
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv', dv, vst, cst, n
    iFrameNamed
    ipureintro
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩
  -- a quorum of StartViewChanges: the DoViewChange to the view's primary
  have hr3 : r < n := Hid.2
  wp_log
  wp_apply (replica.wp_potentialPrimary _ _ _ n (by omega)) $$ [Hr] as Hr
  · iframe Hr Hms; ipureintro; exact Hmslen
  have hn63 : n < 2 ^ 63 := by rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).2
  have hp3 : uint.nat (v'.state'.ViewNumber' % W64 n) < ms.length := by
    rw [Hmslen]; exact replica.umod_lt _ n hn63 (by omega)
  list_elem ms (uint.nat (v'.state'.ViewNumber' % W64 n)) as pm
  ihave #Hapm := BI.BigSepL.bigSepL_lookup Hpm_lookup $$ Haddrs
  have hidx : 0 ≤ sint.Z (v'.state'.ViewNumber' % W64 n) ∧
      sint.Z (v'.state'.ViewNumber' % W64 n) < sint.Z v'.state'.ClusterMembers'.len := by
    have := replica.umod_lt v'.state'.ViewNumber' n hn63 (by omega)
    rw [h3]; word
  rw [if_pos hidx]
  wp_apply (wp_load_slice_index _ (sint.Z (v'.state'.ViewNumber' % W64 n)) ms _ pm (by word))
    $$ [Hms]
  · iframe Hms; ipureintro
    rw [show (sint.Z (v'.state'.ViewNumber' % W64 n)).toNat =
      uint.nat (v'.state'.ViewNumber' % W64 n) by word]
    exact Hpm_lookup
  iintro -
  wp_auto
  ihave #Hcl : ([∗list] f ∈ [Fact.committedBy cw (lg.take (uint.nat v'.state'.CommitNumber'))],
      VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hcfact
  imod VsrReplica.ghost_fact' γ n r (replica.repOf v' lg) _
    (.msg (.doViewChange ⟨uint.nat v'.state'.ViewNumber', lg,
      uint.nat v'.internal'.lastStableViewNumber', uint.nat v'.state'.CommitNumber',
      uint.nat v'.state'.ID'⟩))
    (fun s hs hsn hrp hf => by
      have hcom : CommittedBy s cw (lg.take (uint.nat v'.state'.CommitNumber')) :=
        hf (.committedBy cw _) (by simp)
      have := VsrModel.dvc_own s hs r (uint.nat v'.state'.CommitNumber') (show r < s.n from hsn ▸ hr3)
        (by rw [hrp]; simp [replica.repOf, replica.statusOf, hS])
        (by rw [hrp]; exact Hcommit.1)
        (by rw [hrp]; exact VsrReplica.committedBy_mono s _ Hcommit.2 hcom)
      rw [hrp] at this
      simp only [replica.repOf] at this
      rw [Hid.1]; exact this)
    $$ Hsize Hsys Hrep Hcl with ⟨Hrep, #Hdvf⟩
  wp_apply (replica.wp_sendDoViewChangeToPrimary H rp v' γ tcp C F pm lg Hopnum) $$ [Hr Hsender]
    as %err ⟨Hr, Hsender, #Herr⟩
  · iframe Hr Hsender Hapm Hlog Hdvf
    unfold replica.sendCtx
    iexists me
    iframe HisTCP Hprotos Hcodec Hkit Hsys
    ipureintro; exact Hnet
  cases err with
  | nil =>
    wp_auto
    wp_log
    iapply HΦ
    iexists v'
    iframe Hr
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv', dv, vst, cst, n
    iFrameNamed
    ipureintro
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩
  | ok ii =>
    wp_auto
    wp_log
    wp_log
    iapply HΦ
    iexists v'
    iframe Hr
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv', dv, vst, cst, n
    iFrameNamed
    ipureintro
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
