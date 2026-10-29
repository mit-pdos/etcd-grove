/-
The implementation of `ConfchangeApi.lean`'s sealed definitions and laws (2026-10-29, stage U11),
over `confchange`'s model (`InvConfchange.lean`, `CCApplyC.lean`) and the node API's memberships
(`InvApiDyn.lean`: `stOf`, `memOf`, `cfgOf`, `memApply`). Internal: clients import
`ConfchangeApi.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApiDyn
public import Proof.go_etcd_io.raft.v3.ConfRule

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ApiImpl

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- Go's `confchange` on a membership: `ccApplyM` of the change as `AsV2` makes it, on the
membership's canonical state, without `ccStepB`'s cut. -/
def memApplyGo (o : ConfChangeIM) (m : Membership) : Option Membership :=
  (ccApplyM (ccV2Of o).1 (ccV2Of o).2 (stOf m)).map fun s => memOf s.cfg

/-- A configuration `checkInvariants` accepts tracks the same ids as its membership (a staged
learner is an outgoing voter). -/
theorem memOf_ids_of_inv {s : CCState} (h : CfgInv s) :
    (memOf s.cfg).ids = s.cfg.ids := by
  apply GMap.set_eq; intro k
  simp only [Membership.ids, memOf, CfgM.ids, CfgM.voters, GMap.elem_of_union]
  constructor
  · rintro (((h1 | h1) | h1) | h1)
    · exact .inl (.inl h1)
    · exact .inl (.inr h1)
    · exact .inr h1
    · exact .inl (.inr (h.2.1 k h1).1)
  · rintro ((h1 | h1) | h1)
    · exact .inl (.inl (.inl h1))
    · exact .inl (.inl (.inr h1))
    · exact .inl (.inr h1)

/-- `memApply` is `memApplyGo` cut at `2^62` ids. -/
theorem memApply_eq_go (o : ConfChangeIM) (m : Membership) :
    memApply o m = (memApplyGo o m).filter (fun m' => decide (GMap.size m'.ids < 2 ^ 62)) := by
  unfold memApply memApplyGo ccStepB
  cases h : ccApplyM (ccV2Of o).1 (ccV2Of o).2 (stOf m) with
  | none => rfl
  | some s =>
    simp only [Option.bind_some, Option.map_some, Option.filter_some]
    rw [memOf_ids_of_inv (ccApplyM_inv _ _ h)]
    by_cases hs : GMap.size s.cfg.ids < 2 ^ 62 <;> simp [hs]

theorem gmap_size_eq_of_dom {V W : Type} (a : GMap w64 V) (b : GMap w64 W)
    (h : ∀ k, (a !! k).isSome ↔ (b !! k).isSome) : GMap.size a = GMap.size b := by
  rw [GMap.size_eq_length a b.domList (GMap.nodup_dom_list b)
    (fun k => by rw [GMap.mem_dom_list, h])]
  exact (GMap.size_eq_dom_list_length b).symm

/-- A reachable state's progress map tracks its membership's ids. -/
theorem size_prs_stOf {m : Membership} (hg : CCGood (stOf m)) :
    GMap.size (stOf m).prs = GMap.size m.ids := by
  apply gmap_size_eq_of_dom
  intro k
  rw [← GMap.mem_iff, ← GMap.mem_iff, hg.1 k]
  simp only [stOf_cfg, cfgOf, CfgM.ids, CfgM.voters, Membership.ids,
    GMap.elem_of_union]
  constructor
  · rintro ((h | h) | h)
    · exact .inl (.inl (.inl h))
    · exact .inl (.inl (.inr h))
    · exact .inl (.inr h)
  · rintro (((h | h) | h) | h)
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h
    · have := hg.2.2.2 k h
      exact .inl (.inr this)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The body of a `(Config, ProgressMap)` pair at `m`: the configuration (`ownCfgCC` at `m`'s),
the progress map (read at some fraction) and its `Progress` objects, whose learner flags are the
canonical ones of `m` (`stOf`), a reachable state (`CCGood`). -/
def cfgPairBody (cfg : tracker.Config) (prs : Loc) (m : Membership) : IProp GF :=
  iprop(∃ (pm : GMap w64 Loc) (pvs : GMap w64 tracker.Progress) (dq : DFrac),
    ⌜CCGood (stOf m) ∧ flagsOf pvs = (stOf m).prs⌝ ∗
    ownCfgCC cfg (DFrac.own 1) (cfgOf m) ∗ prs ↦${dq} pm ∗
    ([∗map] _k ↦ pr;pv ∈ pm;pvs, pr ↦ pv))

/-- The size of a pair's progress map, borrowed. -/
theorem cfgPairBody_size (cfg : tracker.Config) (prs : Loc) (m : Membership) :
    cfgPairBody (GF := GF) cfg prs m ⊢ ∃ (M : GMap w64 Loc) (dq : DFrac),
      prs ↦${dq} M ∗ ⌜GMap.size M = GMap.size m.ids⌝ ∗
      (prs ↦${dq} M -∗ cfgPairBody cfg prs m) := by
  unfold cfgPairBody
  iintro ⟨%pm, %pvs, %dq, %Hp, Hc, Hm, Hprs⟩
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  iexists pm, dq
  iframe Hm
  isplitr
  · ipureintro
    rw [← size_prs_stOf Hp.1, ← Hp.2, flagsOf, GMap.map_size_fmap]
    exact gmap_size_eq_of_dom pm pvs Hiff
  · iintro Hm
    iexists pm, pvs, dq
    iframe Hc Hm Hprs
    ipureintro; exact Hp

end defs

end ApiImpl
end EtcdGrove
end Perennial
