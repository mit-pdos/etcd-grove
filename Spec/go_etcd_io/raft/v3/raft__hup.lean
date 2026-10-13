/-
Port of election_proof/spec_raft__hup.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.StepLemmasC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- What `hup` leaves (its postcondition's pure part, 2026-10-13, for `stepFollower`'s
`MsgTimeoutNow`): `r.step` agrees with the role, a protocol step that receives nothing,
the log untouched, the term up by at most one, `r.preVote` and the ghost bounds kept. -/
def HupOk (cfg : GSet w64) (id : w64) (s s' : NState) : Prop :=
  NStateWf s' ∧ Step cfg id (toPState s) [] (toPState s') ∧
  (s'.logst = s.logst ∧ uint.Z s.term ≤ uint.Z s'.term ∧
   uint.Z s'.term ≤ uint.Z s.term + 1 ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh)

/-- `HupOk` at a joint configuration (2026-10-13, reconfiguration stage A2): the step is
`StepC c`, and a node that is not a voter of either half does nothing (it is not
`promotable`). The last conjunct is what lets the simple-configuration statement be derived
at an empty voter set, where `StepC` and `Step` differ (`HupOkC.simple`). -/
def HupOkC (c : CfgM) (id : w64) (s s' : NState) : Prop :=
  NStateWf s' ∧ StepC c id (toPState s) [] (toPState s') ∧
  (s'.logst = s.logst ∧ uint.Z s.term ≤ uint.Z s'.term ∧
   uint.Z s'.term ≤ uint.Z s.term + 1 ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh) ∧
  (id ∉ c.voters → s' = s)

/-- At a simple configuration, `HupOkC` is `HupOk`. -/
theorem HupOkC.simple {cfg lrn : GSet w64} {id : w64} {s s' : NState}
    (h : HupOkC (CfgM.simple cfg lrn) id s s') : HupOk cfg id s s' := by
  refine ⟨h.1, ?_, h.2.2.1⟩
  by_cases hne : cfg = ∅
  · have hs : s' = s := h.2.2.2 (by
      rw [CfgM.voters_simple, hne]; exact GMap.not_elem_of_empty _)
    rw [hs]; exact .refl _
  · exact (step_iff_stepC cfg lrn id hne _ _ _).2 h.2.1

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `hup` checks the node is a promotable voter with no unapplied configuration change,
then campaigns. Genuinely disjunctive — it either campaigns or returns having done
nothing (already a leader, unpromotable, or, since 2026-10-13, a conf-change entry
committed but not applied: `hasUnappliedConfChanges`) — so unlike `campaign` its
postcondition names the model's relation rather than a specific state; the do-nothing
case is `Step.refl`. Since 2026-10-04 `t` is any campaign
type, `campaignPreElection` included: a pre-election is `Step.abandon` and free sends
(`step_campaignState`, `StepLemmas.lean`).

Ghost-free: the `Step` witness is a pure fact handed to the caller, which is where it is
turned into an update of `ownRaftGhost`.

At any configuration since 2026-10-13 (reconfiguration stage A2): the post is `HupOkC`, a
`StepC c` step (a campaign by a voter of either half, asking every other one), and nothing
at a node that is not a voter. The old statement is `raft.hup.specS`. -/
abbrev raft.hup.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType),
  -- `hup` may reach `campaign`, which increments the term -- see the note on
  -- `raft.campaign.spec`.
  uint.Z s.term + 1 < 2 ^ 64 →
  -- a pre-election only with pre-vote on (2026-10-10; see `raft.campaign.spec`)
  (t = campaignPreElection → s.prevote = true) →
  -- `r.step` matches the role; kept by the call
  NStateWf s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysC c r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"hup")) (Val #t))
  {{ (s' : NState), RET #();
      ownRaftPhysC c r id s' ∗ ⌜HupOkC c id s s'⌝ }}

/-- The statement on `ownRaftPhys` (the simple configuration `cfg`) until 2026-10-13,
derived from `raft.hup.spec` by `raft.hup.spec_simple`. -/
abbrev raft.hup.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (t : CampaignType),
  uint.Z s.term + 1 < 2 ^ 64 →
  (t = campaignPreElection → s.prevote = true) →
  NStateWf s →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"hup")) (Val #t))
  {{ (s' : NState), RET #();
      ownRaftPhys cfg r id s' ∗ ⌜NStateWf s'⌝ ∗
      ⌜Step cfg id (toPState s) [] (toPState s')⌝ ∗
      ⌜s'.logst = s.logst ∧ uint.Z s.term ≤ uint.Z s'.term ∧
       uint.Z s'.term ≤ uint.Z s.term + 1 ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh⌝ }}

open Iris.ProofMode in
theorem raft.hup.spec_simple
    (H : raft.hup.spec (GF := GF) (hG := hG)) :
    raft.hup.specS (GF := GF) (hG := hG) := by
  intro cfg r id s t Hnw Hpv Hwf
  iintro %Φ ⟨#Hpkg, Hphys⟩ HΦ
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  iapply H _ r id s t Hnw Hpv Hwf $$ [$Hpkg $Hphys]
  inext
  iintro %s' ⟨Hphys, %Hok⟩
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  have Hok' := Hok.simple
  iapply HΦ
  iframe Hphys
  ipureintro
  exact ⟨Hok'.1, Hok'.2.1, Hok'.2.2⟩

end spec

end EtcdGrove
end Perennial
