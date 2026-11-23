/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/InitiateViewChange.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`initiateViewChange(n)`: the replica changes to the later view `n` (`stepInitVC`), drops its get-state timer, broadcasts StartViewChanges.
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

/-- From a view before `nv`: in view change to `nv`. -/
theorem replica.wp_initiateViewChange (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (v : replica.Replica)
    (nv : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.repInv γ r tcp v ∗ ⌜uint.nat v.state'.ViewNumber' < uint.nat nv⌝ }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"initiateViewChange")) (Val #nv))
    {{ RET #(); ∃ v' : replica.Replica, rp ↦ v' ∗ replica.repInv γ r tcp v' ∗
        ⌜v'.state'.ID' = v.state'.ID' ∧ v'.state'.ClusterMembers' = v.state'.ClusterMembers' ∧
          v'.logger' = v.logger' ∧ v'.network' = v.network' ∧
          v'.state'.ViewNumber' = nv ∧ v'.state'.Status' = W64 1⌝ }} := by
  wp_start as ⟨Hr, Hinv, %Hlt⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_log
  wp_join iprop(∃ l : w64, r_ptr ↦ rp ∗
      rp ↦ ({ v with internal' := { v.internal' with lastStableViewNumber' := l } } :
        replica.Replica) ∗
      ⌜l = if v.state'.Status' = W64 1 then v.internal'.lastStableViewNumber'
        else v.state'.ViewNumber'⌝) with [Hr r] as ⟨%l, r, Hr, %Hl⟩
  · iexists _
    iframe r
    isplitl [Hr]
    · iExactEq Hr; rfl
    ipureintro; simp_all
  · iexists _
    iframe r
    isplitl [Hr]
    · iExactEq Hr; rfl
    ipureintro; simp_all
  have hr3 : r < n := Hid.2
  have hsvc : replica.statusOf v.state'.Status' = .viewChange ↔ v.state'.Status' = W64 1 := by
    unfold replica.statusOf
    constructor
    · intro h; split at h
      · cases h
      · split at h
        · assumption
        · cases h
    · intro h; simp [h]
  have hlnv : uint.nat l = (if (replica.repOf v lg).status = .viewChange then
      (replica.repOf v lg).lnv else (replica.repOf v lg).view) := by
    simp only [replica.repOf, hsvc]
    rw [Hl]
    split <;> rfl
  ihave #Hnil : ([∗list] f ∈ ([] : List Fact), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_step' γ n r (replica.repOf v lg)
    ⟨uint.nat nv, .viewChange, lg, uint.nat l⟩ [] [Fact.msg (.startViewChange (uint.nat nv) r)]
    (fun s => stepInitVC s r (uint.nat nv))
    (fun s hs hsn hrp _ => by
      obtain ⟨hinv, hle⟩ := stepInitVC_inv s r (uint.nat nv) hs (show r < s.n from hsn ▸ hr3)
        (by rw [hrp]; simp only [replica.repOf]; exact Hlt)
      obtain ⟨h1, h2, h3, h4⟩ := VsrReplica.stepInitVC_frame s r (uint.nat nv)
      refine ⟨hinv, hle, by rw [h1, hrp, hlnv]; rfl, h2, h3, h4, ?_⟩
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hf
      subst hf; trivial)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, Hfs'⟩
  icases Hfs' with ⟨#Hsvc, -⟩
  unfold replica.ReplicaStatusViewChange
  wp_auto
  obtain ⟨vf, hvf⟩ : ∃ vf : replica.Replica, vf = { v with
      state' := { v.state' with Status' := W64 1, ViewNumber' := nv },
      internal' := { v.internal' with lastStableViewNumber' := l, getStateTimer' := null } } :=
    ⟨_, rfl⟩
  ihave Hr : rp ↦ vf $$ [Hr]
  · iExactEq Hr; rw [hvf]
  have hvfM : vf.state'.ClusterMembers' = v.state'.ClusterMembers' := by rw [hvf]
  have hvfLg : vf.logger' = v.logger' := by rw [hvf]
  have hvfI : vf.state'.ID' = v.state'.ID' := by rw [hvf]
  have hvfN : vf.network' = v.network' := by rw [hvf]
  irename Hlogger => Hlogger0
  ihave #Hlogger : log.slog.isLogger vf.logger' $$ []
  · rw [hvfLg]; iexact Hlogger0
  ihave %Hmlen := ownSlice_len $$ Hms
  have h3 : v.state'.ClusterMembers'.len = W64 n := by
    rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).1
  ihave HI : (∃ (i : w64) (mem : ipv4port.IPv4Port),
      "i" ∷ i_ptr ↦ i ∗ "member" ∷ member_ptr ↦ mem ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ : IProp GF) $$ [i member]
  · iexists _, _; iframe; ipureintro; word
  wp_for HI
  rw [h3]
  wp_if_destruct
  · have hi3 : sint.nat i < ms.length := by
      have := (replica.len_of_slice _ _ Hmlen).2; rw [Hmslen] at this ⊢; word
    list_elem ms (sint.nat i) as m
    rw [if_pos (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z v.state'.ClusterMembers'.len by
      rw [h3]; word)]
    wp_apply (wp_load_slice_index _ (sint.Z i) ms _ m (by word)) $$ [Hms]
    · iframe Hms; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hm_lookup
    iintro -
    wp_auto
    wp_apply (H.wp_String_ptr member_ptr (DFrac.own 1) m) $$ [member] as member
    · iexact member
    wp_log
    ihave #Ham := BI.BigSepL.bigSepL_lookup Hm_lookup $$ Haddrs
    wp_apply (replica.wp_sendStartViewChange H rp vf γ tcp C F m nv) $$ [Hr Hsender]
      as %err ⟨Hr, Hsender, #Herr⟩
    · iframe Hr Hsender Ham
      isplitl []
      · unfold replica.sendCtx
        iexists me
        iframe HisTCP Hprotos Hcodec Hkit Hsys
        ipureintro; rw [hvfN]; exact Hnet
      rw [hvfI, Hid.1]; iexact Hsvc
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; word
    | ok ii =>
      wp_auto
      wp_apply (H.wp_String_ptr member_ptr (DFrac.own 1) m) $$ [member] as member
      · iexact member
      wp_log
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; word
  have hvc : replica.statusOf vf.state'.Status' = .viewChange := by
    simp [replica.statusOf, hvf]
  have hvfV : vf.state'.ViewNumber' = nv := by rw [hvf]
  have hnp : ¬ replica.IsNormalPrimary n vf r := by
    unfold replica.IsNormalPrimary; rw [hvc]; simp
  ihave Hdvs := BI.BigSepM.bigSepM_mono (M := GMap w64)
    (fun {k e'} _ => replica.dvOk_mono γ v vf k e' (by
      unfold replica.Live; intro hl
      left
      rcases hl with hl | ⟨hl, -⟩
      · rw [hvfV] at hl; omega
      · rw [hvfV] at hl; subst hl; exact Hlt)) $$ Hdvs
  ihave Hpks := BI.BigSepM.bigSepM_mono (M := GMap w64)
    (fun {k e'} _ => replica.pokOk_notPrimary γ n tcp v vf r k e' hnp) $$ Hpks
  ihave Hgst : replica.gstOk n vf r $$ []
  · unfold replica.gstOk; ileft; ipureintro; rw [hvf]
  iapply HΦ
  iexists vf
  iframe Hr
  isplitl
  · iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, n
    have hrepF : replica.repOf vf lg = ⟨uint.nat nv, .viewChange, lg, uint.nat l⟩ := by
      simp only [replica.repOf, hvc, hvfV]; rw [hvf]
    have e2 : vf.time' = v.time' := by rw [hvf]
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
    have hmv : replica.mineView vf = uint.nat l := by
      unfold replica.mineView; rw [hvc]; simp; rw [hvf]
    have hmv0 : replica.mineView v = uint.nat l := by
      unfold replica.mineView
      rw [hlnv]; simp only [replica.repOf]
      split <;> simp_all
    rw [hrepF, hvfM, hvfN, e2, hvfLg, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e16, e17, hvfI]
    iFrameNamed
    ipureintro
    refine ⟨Hid, Hmslen, Hnet, Htime, by simp [replica.StatusOk, hvf],
      fun h => (by rw [hvc] at h; cases h), Hopnum, ⟨Hcommit.1, ?_⟩,
      ⟨Hmine.1, Hmine.2.1, by rw [hmv, ← hmv0]; exact Hmine.2.2⟩, Htmine, fun h => absurd h hnp⟩
    rw [hvfV]; omega
  ipureintro
  exact ⟨hvfI, hvfM, hvfLg, hvfN, hvfV, by rw [hvf]⟩

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
