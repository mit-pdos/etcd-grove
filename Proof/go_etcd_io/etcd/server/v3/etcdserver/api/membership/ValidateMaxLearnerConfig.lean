/-
Proof of `Spec/.../membership/ValidateMaxLearnerConfig.lean` (claim #34, stage 2, 2026-11-25): the
range over the members counting the learners (each member's `IsLearner` read from its owned
fields), then the comparison: `ErrTooManyLearners` or nil. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.ValidateMaxLearnerConfig

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

theorem membership.ValidateMaxLearnerConfig.wp_proof :
    membership.ValidateMaxLearnerConfig.spec (GF := GF) (hG := hG) := by
  intro ml sl ms scale
  wp_start as Hms
  iunfold membership.membersAt at Hms
  icases Hms with ⟨Hsl, Hown⟩
  ihave Hmi : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, #Hev, -⟩
  ihave #NTM := EtcdGrove.errorsNewVars_mem
    (X := go_etcd_io.etcd.server.v3.etcdserver.api.membership.ErrTooManyLearners)
    (m := go!"membership: too many learner members in cluster")
    (by unfold go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipErrMsgs; simp) $$ Hev
  iunfold EtcdGrove.errorsNewVar at NTM
  icases NTM with ⟨%xe, #HeTM, -⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  -- `for _, m := range members { if m.IsLearner { numLearners++ } }`
  ihave HF : (∃ (k n : w64) (x : Loc),
      "i" ∷ i_ptr ↦ k ∗ "numLearners" ∷ numLearners_ptr ↦ n ∗ "m" ∷ m_ptr ↦ x ∗
      "Hsl" ∷ sl ↦* ms ∗ "Hown" ∷ ([∗list] m ∈ ms, membership.ownMember m) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sl.len⌝ : IProp GF)
    $$ [i numLearners m Hsl Hown]
  · iexists W64 0, _, _
    iframe
    ipureintro
    exact ⟨by decide, by have := Hlen.2; word⟩
  wp_for HF
  obtain ⟨Hk1, Hk2⟩ := Hk
  (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := ⟨Hk1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    list_elem ms (sint.nat k) as mv
    wp_apply (wp_load_slice_index sl (sint.Z k) ms (DFrac.own 1) mv Hk1) $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hmv_lookup
    (try wp_auto)
    icases (BigSepL.bigSepL_lookup_acc (Φ := fun _ (m : Loc) => membership.ownMember (GF := GF) m)
      Hmv_lookup).1 $$ Hown with ⟨Hm1, Hmcl⟩
    iunfold membership.ownMember at Hm1
    icases Hm1 with ⟨%mid, Hm1⟩
    iunfold membership.memberIs at Hm1
    icases Hm1 with ⟨%Hmnn, %pu, %cu, %il, %nm, %pus, %cus, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
    (try wp_auto)
    ihave Hm1 : membership.ownMember (GF := GF) mv $$ [Hid Hpu Hil Hnm Hcu Hpus Hcus]
    · iunfold membership.ownMember
      iexists mid
      iunfold membership.memberIs
      isplitr
      · ipureintro; exact Hmnn
      iexists pu, cu, il, nm, pus, cus
      iframe
    ihave Hown := Hmcl $$ Hm1
    have hset : ms.set (sint.nat k) mv = ms := by
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 Hmv_lookup
      rw [← hget]; exact List.set_getElem_self hlt
    rw [hset]
    wp_if_destruct
    all_goals
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1, _, _
      iframe
      isplitl [Hown]
      · iexact Hown
      ipureintro
      exact ⟨by word, by word⟩
  · (try wp_auto)
    wp_if_destruct
    all_goals (try wp_auto)
    all_goals wp_if_destruct
    all_goals (try wp_auto)
    all_goals
      iapply HΦ
      iunfold membership.membersAt
      iframe
end proof

end EtcdGrove
end Perennial
