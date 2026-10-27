/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/Member__Clone.lean`. Lean-first (no Rocq counterpart); unit P1b (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member__Clone

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- The member's fields, the clone's, both URL slices copied: the return. -/
local macro "clone_fin" : tactic => `(tactic| (
  (try wp_auto)
  iapply HΦ
  isplitl [Hid Hpu Hil Hnm Hcu Hpus Hcus]
  · iunfold membership.memberAt
    isplitr
    · ipureintro; exact Hmnn
    iexists _, _
    iframe
  · iunfold membership.memberIs
    isplitr
    · ipureintro; exact Hr0nn
    icases Hpm with ⟨%npu, Hpm1, Hpm2⟩
    icases Hcm with ⟨%ncu, Hcm1, Hcm2⟩
    iexists npu, ncu, mm.isLearner, mm.name, mm.peerURLs, mm.clientURLs
    iframe))

set_option hygiene false in
/-- After the `PeerURLs` copy: the `ClientURLs` copy, then the return. -/
local macro "clone_tail" : tactic => `(tactic| (
  (try wp_auto)
  ihave %Hcul := ownSlice_len _ _ _ $$ Hcus
  wp_if_destruct
  · (try wp_auto)
    ihave Hcm : iprop(∃ ncu : GoSlice, membership.mClientURLsAddr «$r0_ptr» ↦ ncu ∗ ncu ↦* mm.clientURLs)
      $$ [ClientURLs]
    · iexists slice.nil; iframe ClientURLs
      have hc : mm.clientURLs = [] := List.eq_nil_of_length_eq_zero (by rw [Hcul.1]; rfl)
      rw [hc]; iapply ownSlice_nil
    clone_fin
  · wp_apply wp_slice_make2 (V := GoString) _ as %ncu ⟨Hncu, -⟩
    · ipureintro; exact Hcul.2
    (try wp_auto)
    wp_apply +noauto wp_slice_copy $$ [Hncu Hcus] as %n2 ⟨-, Hncu, Hcus⟩
    · iframe
    have Hcp : (mm.clientURLs.take (List.replicate (sint.nat cu.len) (zero_val GoString)).length ++
        (List.replicate (sint.nat cu.len) (zero_val GoString)).drop mm.clientURLs.length) = mm.clientURLs := by
      rw [List.length_replicate, List.take_of_length_le (by rw [Hcul.1]; exact Nat.le_refl _),
        List.drop_of_length_le (by rw [List.length_replicate, Hcul.1]; exact Nat.le_refl _),
        List.append_nil]
    rw [Hcp]
    ihave Hcm : iprop(∃ ncu : GoSlice, membership.mClientURLsAddr «$r0_ptr» ↦ ncu ∗ ncu ↦* mm.clientURLs)
      $$ [ClientURLs Hncu]
    · iexists ncu; iframe
    clone_fin))

theorem membership.Member.Clone.wp_proof :
    membership.Member.Clone.spec (GF := GF) (hG := hG) := by
  intro m q mm
  wp_start as Hm
  iunfold membership.memberAt at Hm
  icases Hm with ⟨%Hmnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
  wp_auto
  rw [decide_eq_false Hmnn]
  wp_auto
  ihave %Hr0nn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamed «$r0»
  iStructNamed RaftAttributes
  iStructNamed Attributes
  -- `PeerURLs`
  ihave %Hpul := ownSlice_len _ _ _ $$ Hpus
  wp_if_destruct
  · (try wp_auto)
    ihave Hpm : iprop(∃ npu : GoSlice, membership.mPeerURLsAddr «$r0_ptr» ↦ npu ∗ npu ↦* mm.peerURLs)
      $$ [PeerURLs]
    · iexists slice.nil; iframe PeerURLs
      have hp : mm.peerURLs = [] := List.eq_nil_of_length_eq_zero (by rw [Hpul.1]; rfl)
      rw [hp]; iapply ownSlice_nil
    clone_tail
  · wp_apply wp_slice_make2 (V := GoString) _ as %npu ⟨Hnpu, -⟩
    · ipureintro; exact Hpul.2
    (try wp_auto)
    wp_apply +noauto wp_slice_copy $$ [$Hnpu $Hpus] as %n1 ⟨-, Hnpu, Hpus⟩
    have Hcp : (mm.peerURLs.take (List.replicate (sint.nat pu.len) (zero_val GoString)).length ++
        (List.replicate (sint.nat pu.len) (zero_val GoString)).drop mm.peerURLs.length) = mm.peerURLs := by
      rw [List.length_replicate, List.take_of_length_le (by rw [Hpul.1]; exact Nat.le_refl _),
        List.drop_of_length_le (by rw [List.length_replicate, Hpul.1]; exact Nat.le_refl _),
        List.append_nil]
    rw [Hcp]
    ihave Hpm : iprop(∃ npu : GoSlice, membership.mPeerURLsAddr «$r0_ptr» ↦ npu ∗ npu ↦* mm.peerURLs)
      $$ [PeerURLs Hnpu]
    · iexists npu; iframe
    clone_tail

end proof

end EtcdGrove
end Perennial
