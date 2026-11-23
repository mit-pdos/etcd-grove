/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/CheckCommitTimeout.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`checkCommitTimeout`: the normal primary broadcasts its commit number (`commit_own`).
(Proved.)
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

/-- The timers' second check. -/
theorem replica.wp_checkCommitTimeout (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"checkCommitTimeout")) (Val #()))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as Hown
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply H.wp_Done $$ [Hct] as %b Hct
  · iexact Hct
  cases b
  · wp_auto
    close_own
  try wp_auto
  wp_apply (replica.wp_potentialPrimary rp v ms n (by omega)) $$ [Hr] as Hr
  · iframe Hr Hms; ipureintro; exact Hmslen
  try wp_auto
  wp_if_destruct
  rotate_left
  · close_own
  wp_if_destruct
  rotate_left
  · close_own
  wp_log
  have hnp : replica.statusOf v.state'.Status' = .normal := by simp [replica.statusOf, Hif]
  ihave #Hcf1 : ([∗list] f ∈ [Fact.committedBy cw (lg.take (uint.nat v.state'.CommitNumber'))],
      VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hcfact
  imod VsrReplica.ghost_fact' γ n r _ _
    (.msg (.commit (uint.nat v.state'.ViewNumber') (uint.nat v.state'.CommitNumber')
      (uint.nat v.state'.ID')))
    (fun s hs hsn hrp hf => by
      have hc := hf _ (List.mem_singleton_self _)
      obtain ⟨w, hw, hcw⟩ := hc
      have := VsrModel.commit_own s hs r (uint.nat v.state'.CommitNumber') (hsn ▸ Hid.2)
        (by simp only [hrp, replica.repOf]; left; exact hnp)
        (by simp only [hrp, replica.repOf]; exact Hcommit.1)
        (by simp only [hrp, replica.repOf]; exact ⟨w, Nat.le_trans hw Hcommit.2, hcw⟩)
      simp only [hrp, replica.repOf] at this
      rw [Hid.1]; exact this)
    $$ Hsize Hsys Hrep Hcf1 with ⟨Hrep, #Hcm⟩
  ihave %Hmlen := ownSlice_len $$ Hms
  ihave HI : (∃ (i : w64) (mem : ipv4port.IPv4Port) (mi : w64),
      "i" ∷ i_ptr ↦ i ∗ "member" ∷ member_ptr ↦ mem ∗ "mi" ∷ mi_ptr ↦ mi ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ : IProp GF) $$ [i member mi]
  · iexists _, _, _; iframe; ipureintro; word
  have h3 : v.state'.ClusterMembers'.len = W64 n := by
    rw [← Hmslen]; exact (replica.len_of_slice _ _ Hmlen).1
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
    wp_if_destruct
    · -- itself: continue
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro; word
    ihave #Ham := BI.BigSepL.bigSepL_lookup Hm_lookup $$ Haddrs
    wp_apply (replica.wp_sendCommitToBackup H rp v γ tcp C F m v.state'.CommitNumber') $$ [Hr Hsender]
      as %err ⟨Hr, Hsender, -⟩
    · iframe Hr Hsender Ham Hcm
      unfold replica.sendCtx
      iexists me
      iframe HisTCP Hprotos Hcodec Hkit Hsys
      ipureintro; exact Hnet
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro; word
  wp_apply H.wp_Reset $$ [Hct] as Hct
  · iexact Hct
  close_own

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
