/-
The lemmas of a tracker rebuilt from a snapshot's `ConfState` (`MakeProgressTracker`,
`confchange.Restore`, `switchToConfig`): what `raft.restore` used until 2026-10-28 and
`raft.appliedSnap` uses since (stage U0: the configuration switches when the snapshot is applied).
Moved from `raft__restore.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApplyConfC
public import Proof.go_etcd_io.raft.v3.LemmasConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A list without repeats is a permutation of the elements of its set. -/
theorem perm_elements_listToSet (l : List w64) (h : l.Nodup) :
    l ≡ₚ GMap.elements (GMap.listToSet l) := by
  refine (List.perm_ext_iff_of_nodup h (GMap.NoDup_elements _)).2 ?_
  intro k; rw [GMap.elem_of_elements, GMap.elem_of_list_to_set]

theorem gset_size_union_le (X Y : GSet w64) :
    GMap.size (X ∪ Y) ≤ GMap.size X + GMap.size Y := by
  rw [GMap.size_union_alt]
  have := GMap.subseteq_size (GMap.difference_subseteq Y X)
  omega

/-- The progress map `Restore` builds for the lists `cl` has at most as many entries as the
lists have ids. -/
theorem restore_prs_size (cl : CSLists) (Hvnd : cl.voters.Nodup) (Hlnd : cl.learners.Nodup)
    (Hond : cl.outgoing.Nodup)
    (Hsz : (cl.voters.length + cl.learners.length + cl.outgoing.length + cl.learnersNext.length :
      Int) ≤ 2 ^ 62)
    (prs : GMap w64 Loc) (al : Bool)
    (Hprs : domSet prs =
      domSet (cfgStateC (csCfgM cl.outgoing cl.voters cl.learners cl.learnersNext al)).prs) :
    (GMap.size prs : Int) ≤ 2 ^ 62 := by
  have Hd : domSet prs = (GMap.listToSet cl.voters ∪ GMap.listToSet cl.outgoing) ∪
      GMap.listToSet cl.learners := by
    rw [Hprs]
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom']
    simp only [cfgStateC, csCfgM, CfgM.voters]
    rw [cfgFlags_mem]
    simp only [GMap.elem_of_union]
  have h1 := GMap.size_dom prs
  rw [Hd] at h1
  have h2 := gset_size_union_le (GMap.listToSet cl.voters ∪ GMap.listToSet cl.outgoing)
    (GMap.listToSet cl.learners)
  have h3 := gset_size_union_le (GMap.listToSet cl.voters) (GMap.listToSet cl.outgoing)
  rw [GMap.size_list_to_set _ Hvnd, GMap.size_list_to_set _ Hond] at h3
  rw [GMap.size_list_to_set _ Hlnd] at h2
  have : (0 : Int) ≤ cl.learnersNext.length := by omega
  omega

/-- What `confchange.Restore` builds for a `ConfState` denoting `c`, as `switchToConfig` takes
it (`ownConfigC`): its `Progress` values are some `pvs` whose learner flags are `c`'s. -/
theorem ownConfigC_of_restore (c : CfgM) (cfgv : tracker.Config) (prsm : Loc)
    (prs : GMap w64 Loc) (Hinv : CfgInv (cfgStateC c))
    (Hdom : domSet prs = domSet (cfgStateC c).prs) (Hsz : (GMap.size prs : Int) ≤ 2 ^ 62)
    (P : w64 → Progress → Prop) (HP : ∀ k p, P k p → (cfgStateC c).prs !! k = some p.learner) :
    ⊢ ownCfgCC (GF := GF) cfgv (DFrac.own 1) c -∗ prsm ↦$□ prs -∗
      ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress pr p ∗ ⌜P k p⌝) -∗
      ∃ pvs, ownConfigC c cfgv prsm prs pvs := by
  iintro Hc #Hprsm Hprogs
  ihave Hprogs : ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress (GF := GF) pr p ∗
      ⌜(cfgStateC c).prs !! k = some p.learner⌝) $$ [Hprogs]
  · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
    intro k pr _
    iintro ⟨%p, Hp, %Hpk⟩
    iexists p
    iframe Hp
    ipureintro; exact HP k p Hpk
  icases bigSepM_exist_sepM2 prs
    (fun k pr (p : Progress) => iprop(ownProgress (GF := GF) pr p ∗
      ⌜(cfgStateC c).prs !! k = some p.learner⌝))
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
      exact (Hfl k pr p hpr hp).symm
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
  refine ⟨?_, ?_, ?_, Hsz⟩
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

end lemmas

end EtcdGrove
end Perennial
