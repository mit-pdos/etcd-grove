/-
What `confchange.Restore` builds, as `switchToConfig` takes it (`ownConfigC`): shared by
`raft.restore` (a snapshot's configuration) and `newRaft` (2026-10-20, witness support: the storage's
conf state, possibly with a witness). Until 2026-10-20 private to `raft__restore.lean`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTrackerC
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRestore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- What `confchange.Restore` builds for a `ConfState` denoting `c`, as `switchToConfig` takes
it (`ownConfigC`): its `Progress` values are some `pvs` whose learner flags are `c`'s, and whose
witness flag is the configuration's witness's (2026-10-20, witness support; until then none). -/
theorem ownConfigC_of_restore (c : CfgM) (cfgv : tracker.Config) (prsm : Loc)
    (prs : GMap w64 Loc) (Hinv : CfgInv (cfgStateC c))
    (Hdom : domSet prs = domSet (cfgStateC c).prs) (Hsz : (GMap.size prs : Int) ≤ 2 ^ 62)
    (P : w64 → Progress → Prop)
    (HP : ∀ k p, P k p → (cfgStateC c).prs !! k = some p.learner ∧
      p.witness = decide (k = c.wit ∧ c.wit ≠ W64 0))
    (H0 : W64 0 ∉ domSet prs) :
    ⊢ ownCfgCC (GF := GF) cfgv (DFrac.own 1) c -∗ prsm ↦$□ prs -∗
      ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗ ⌜P k p⌝) -∗
      ∃ pvs, ownConfigC c cfgv prsm prs pvs := by
  iintro Hc #Hprsm Hprogs
  ihave Hprogs : ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress (GF := GF) pr p ∗
      ⌜(cfgStateC c).prs !! k = some p.learner ∧
        p.witness = decide (k = c.wit ∧ c.wit ≠ W64 0)⌝) $$ [Hprogs]
  · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
    intro k pr _
    iintro ⟨%p, Hp, %Hpk⟩
    iexists p
    iframe Hp
    ipureintro; exact HP k p Hpk
  icases bigSepM_exist_sepM2 prs
    (fun k pr (p : Progress) => iprop(ownProgress (GF := GF) pr p ∗
      ⌜(cfgStateC c).prs !! k = some p.learner ∧
        p.witness = decide (k = c.wit ∧ c.wit ≠ W64 0)⌝))
    $$ Hprogs with ⟨%pvs, Hprogs⟩
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  icases BigSepM2.bigSepM2_sep_eqv.1 $$ Hprogs with ⟨Hprogs, Hfl⟩
  ihave %Hfl := BigSepM2.bigSepM2_pure_intro $$ Hfl
  -- the learner flags of `pvs` are the configuration's
  have Htf : trkFlags pvs = (cfgStateC c).prs := by
    apply GMap.map_eq; intro k
    rw [trkFlags_lookup]
    cases hp : pvs !! k with
    | some p =>
      obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1
        ((Hiff k).2 (by show (pvs !! k).isSome = true; rw [hp]; rfl))
      exact (Hfl k pr p hpr hp).1.symm
    | none =>
      cases hc : (cfgStateC c).prs !! k with
      | none => rfl
      | some b =>
        exfalso
        have hk : k ∈ domSet prs := by
          rw [Hdom, GMap.elem_of_dom', GMap.mem_iff, hc]; rfl
        rw [GMap.elem_of_dom', GMap.mem_iff] at hk
        have h2 : (pvs !! k).isSome = true := (Hiff k).1 hk
        rw [hp] at h2
        exact absurd h2 (by decide)
  iexists pvs
  unfold ownConfigC
  iframe Hc Hprsm Hprogs
  ipureintro
  refine ⟨?_, ?_, ?_, Hsz, ?Hw⟩
  case Hw =>
    -- the configuration's witness alone is one (2026-10-20; until then witness-free)
    intro k p hp
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1
      ((Hiff k).2 (by show (pvs !! k).isSome = true; rw [hp]; rfl))
    exact ⟨(Hfl k pr p hpr hp).2, ne0_of_dom H0 hpr⟩
  · rw [Htf]; exact Hinv
  · rw [Hdom]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom']
    simp only [cfgStateC, CfgM.ids]
    rw [cfgFlags_mem, GMap.elem_of_union]
  · intro k p hp
    have h1 : (cfgStateC c).prs !! k = some p.learner := by
      rw [← Htf, trkFlags_lookup, hp]; rfl
    simp only [cfgStateC] at h1
    rw [cfgFlags_lookup] at h1
    by_cases hv : k ∈ c.voters
    · rw [ite_eq_left hv] at h1
      have hl : k ∉ c.learners := by
        intro hl
        obtain ⟨ho, hi, -⟩ := Hinv.2.2.1 k hl
        unfold CfgM.voters at hv
        rcases (GMap.elem_of_union _ _ _).1 hv with h | h
        · exact hi h
        · exact ho h
      rw [← Option.some.inj h1]; simp [hl]
    · rw [ite_eq_right hv] at h1
      by_cases hl : k ∈ c.learners
      · rw [ite_eq_left hl] at h1; rw [← Option.some.inj h1]; simp [hl]
      · rw [ite_eq_right hl] at h1; cases h1


theorem ownCfgCC_cast (cfgv : tracker.Config) (dq : DFrac) (c1 c2 : CfgM) (h : c1 = c2) :
    ownCfgCC (GF := GF) cfgv dq c1 ⊢ ownCfgCC cfgv dq c2 := h ▸ .rfl

end proof

end EtcdGrove
end Perennial
