/-
Port of election_proof/proof_raft__hup.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__hup
public import Spec.go_etcd_io.raft.v3.raft__campaign
public import Spec.go_etcd_io.raft.v3.raft__promotable
public import Spec.go_etcd_io.raft.v3.raft__hasUnappliedConfChanges
-- `step_campaignState`; Rocq's `postulates_raft__hup.v` imports `step_lemmas` too
public import Proof.go_etcd_io.raft.v3.StepLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
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
- `r.hasUnappliedConfChanges()` (since 2026-10-13, reconfiguration stage D, a real
  answer: a conf-change entry at `(applied, committed]`) refuses the campaign: log and
  return, `Step.refl`. (Until then it returned `false`, the log having no conf-change
  entry, and its logging arm was dead.)

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
  intro c r id s t Hnowrap Hpv Hwf
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  by_cases Hrl : s.role = .leader
  · -- already a leader: log and return, having done nothing
    rw [Hrl, decide_eq_true (by rfl)]
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_raft_logC
    iapply HΦ $$ %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, .refl _, ⟨rfl, Int.le_refl _, by omega, rfl, rfl⟩, fun _ => rfl⟩
  · -- not a leader
    have Hnl : stateW64 s.role ≠ W64 2 := by
      cases h : s.role <;> simp_all [stateW64] <;> decide
    rw [decide_eq_false Hnl]
    wp_auto
    wp_apply wp_raft_promotable $$ [$Hphys] as %b ⟨Hphys, %Hb⟩
    cases b with
    | true =>
      -- a voter, so it may campaign
      obtain ⟨Hin, Hsn⟩ := of_decide_eq_true Hb.symm
      wp_auto
      wp_apply wp_raft_hasUnappliedConfChanges _ _ _ _ Hsn $$ [$Hphys] as %hc ⟨Hphys, -⟩
      cases hc with
      | true =>
        -- (2026-10-13) a conf-change entry committed but not applied: log and return,
        -- having done nothing
        wp_auto
        wp_apply raft.wp_load_idC $$ Hphys as Hphys
        wp_apply raft.wp_load_TermC $$ Hphys as Hphys
        wp_raft_logC
        iapply HΦ $$ %s
        iframe Hphys
        ipureintro
        exact ⟨Hwf, .refl _, ⟨rfl, Int.le_refl _, by omega, rfl, rfl⟩, fun _ => rfl⟩
      | false =>
      wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_apply raft.wp_load_TermC $$ Hphys as Hphys
      wp_raft_logC
      wp_apply wp_raft_campaign _ _ _ _ _ Hrl Hin Hnowrap Hpv $$ [$Hphys]
        as %peers %pvs ⟨%Hpeers, Hphys⟩
      iapply HΦ
      iframe Hphys
      ipureintro
      refine ⟨nstateWf_prvals _ _ (nstateWf_campaignState _ _ _ _ _),
        stepC_campaignState c _ _ _ _ _ Hrl Hin Hnowrap Hpeers _, ?_, fun h => absurd Hin h⟩
      unfold campaignState
      refine ⟨by split <;> rfl, ?_⟩
      split <;> simp only [sendMsgs, becomePrecandidate, becomeCandidate, resetTo, resetTo0] <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> first | exact True.intro | rfl | word
    | false =>
      -- unpromotable: log and return, having done nothing
      wp_auto
      wp_apply raft.wp_load_idC $$ Hphys as Hphys
      wp_raft_logC
      iapply HΦ $$ %s
      iframe Hphys
      ipureintro
      exact ⟨Hwf, .refl _, ⟨rfl, Int.le_refl _, by omega, rfl, rfl⟩, fun _ => rfl⟩

end proof

end EtcdGrove
end Perennial
