/-
Port of election_proof/proof_raft__hup.v.
-/
import EtcdGrove.Raft.Spec.raft__hup
import EtcdGrove.Raft.Spec.raft__campaign
import EtcdGrove.Raft.Spec.raft__promotable
import EtcdGrove.Raft.Spec.raft__hasUnappliedConfChanges
-- `step_campaignState`; Rocq's `postulates_raft__hup.v` imports `step_lemmas` too
import EtcdGrove.Raft.StepLemmas

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `hup` has three early returns and one real path, and the postcondition
is disjunctive to match. The three early returns leave the struct
alone, so they hand back `s` itself and `Step.refl`; the last path is
`campaign`, whose postcondition names the resulting state outright and
whose `Step` witness is `step_campaignState`.

Two of the branches are decided rather than taken:

- `r.state == StateLeader` is decided by the loaded
  `stateW64 s.role` together with injectivity of
  `stateW64` -- the `≠ W64 2` fact in the non-leader branch is the
  same computation `becomeCandidate` does for its panic check.
- `r.hasUnappliedConfChanges()` returns `false` (no reconfiguration is
  in scope), so its logging arm is dead code.

`promotable` is the one branch genuinely taken both ways: its result is
`decide (r.id ∈ cfg ∧ snap = none)`, which is exactly the
`id ∈ cfg` premise `campaign` needs together with the no-pending-
snapshot premise `hasUnappliedConfChanges` and `campaign` need (since
2026-10-02), so the two arms are "campaign" and "return": a node with
a pending snapshot logs and returns, `Step.refl`. -/
theorem raft.hup.wp_proof
    (wp_raft_campaign : raft.campaign.spec (GF := GF) (hG := hG))
    (wp_raft_promotable : raft.promotable.spec (GF := GF) (hG := hG))
    (wp_raft_hasUnappliedConfChanges : raft.hasUnappliedConfChanges.spec (GF := GF) (hG := hG)) :
    raft.hup.spec (GF := GF) (hG := hG) := by
  intro cfg r id s t Hnowrap Hwf
  wp_start as Hphys
  wp_alloc r_ptr as r; wp_pures; wp_alloc t_ptr as t; wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_state $$ Hphys as Hphys
  wp_pures
  by_cases Hrl : s.role = .leader
  · -- already a leader: log and return, having done nothing
    rw [Hrl, decide_eq_true (by rfl)]
    wp_pures; wp_load; wp_pures
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_pures
    wp_raft_log
    wp_pures; iclear r t
    iapply HΦ $$ %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, .refl _⟩
  · -- not a leader
    have Hnl : stateW64 s.role ≠ W64 2 := by
      cases h : s.role <;> simp_all [stateW64] <;> decide
    rw [decide_eq_false Hnl]
    wp_pures; wp_load; wp_pures
    wp_apply wp_raft_promotable $$ [$Hphys] as %b ⟨Hphys, %Hb⟩
    wp_pures
    cases b with
    | true =>
      -- a voter, so it may campaign
      obtain ⟨Hin, Hsn⟩ := of_decide_eq_true Hb.symm
      wp_pures; wp_load; wp_pures
      wp_apply wp_raft_hasUnappliedConfChanges _ _ _ _ Hsn $$ [$Hphys] as Hphys
      wp_pures; wp_load; wp_pures
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_pures; wp_load; wp_pures
      wp_apply raft.wp_load_Term $$ Hphys as Hphys
      wp_pures
      wp_raft_log
      wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear r t
      wp_apply wp_raft_campaign _ _ _ _ _ Hrl Hin Hnowrap $$ [$Hphys]
        as %peers %pvs ⟨%Hpeers, Hphys⟩
      wp_pures
      iapply HΦ
      iframe Hphys
      ipureintro
      exact ⟨nstateWf_prvals _ _ (nstateWf_campaignState _ _ _ _),
        step_campaignState cfg _ _ _ _ _ Hrl Hin Hnowrap Hpeers⟩
    | false =>
      -- unpromotable: log and return, having done nothing
      wp_pures; wp_load; wp_pures
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_pures
      wp_raft_log
      wp_pures; iclear r t
      iapply HΦ $$ %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, .refl _⟩

end proof

end EtcdGrove
end Perennial
