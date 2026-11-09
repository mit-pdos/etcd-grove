/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Durable__equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Durable__equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Config__Equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `Durable`'s equality, field by field. -/
theorem Durable.eq_iff (d e : Durable) :
    d = e ↔ d.currentTerm = e.currentTerm ∧ d.votedFor = e.votedFor ∧ d.log = e.log ∧
      d.commitIndex = e.commitIndex ∧ d.config = e.config := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; cases d; cases e; simp_all

theorem Durable.equal.wp_proof (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG))
    (wp_ConfigEqual : Config.Equal.spec (GF := GF) (hG := hG)) :
    Durable.equal.spec (GF := GF) (hG := hG) := by
  intro g d h e
  wp_start as ⟨#Hd, #He⟩
  iunfold durableRO at Hd He
  icases Hd with ⟨%Hd1, #Hdl, #Hdc⟩
  icases He with ⟨%He1, #Hel, #Hec⟩
  wp_auto
  have ht := sint_eq_iff _ _ _ _ Hd1.1 He1.1
  have hv := uint_eq_iff _ _ _ _ Hd1.2.1 He1.2.1
  have hc := sint_eq_iff _ _ _ _ Hd1.2.2 He1.2.2
  by_cases h1 : d.currentTerm = e.currentTerm
  · rw [decide_eq_true (ht.2 h1)]
    wp_auto
    by_cases h2 : d.votedFor = e.votedFor
    · rw [decide_eq_true (hv.2 h2)]
      wp_auto
      wp_apply wp_EntriesEqual _ _ _ _ $$ [Hdl Hel] as -
      · iframe Hdl Hel
      by_cases h3 : d.log = e.log
      · rw [decide_eq_true h3]
        wp_auto
        by_cases h4 : d.commitIndex = e.commitIndex
        · rw [decide_eq_true (hc.2 h4)]
          wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Config.TypeAssumptions.ptr_Equal_unfold.method_unfold]
          wp_auto
          wp_apply wp_ConfigEqual _ _ _ _ $$ [Hdc Hec] as -
          · iframe Hdc Hec
          try wp_auto
          have : decide (d.config = e.config) = decide (d = e) := by
            apply decide_eq_decide.2; rw [Durable.eq_iff]; simp [h1, h2, h3, h4]
          rw [this]
          iapply HΦ; ipureintro; trivial
        · rw [decide_eq_false (fun x => h4 (hc.1 x))]
          wp_auto
          rw [decide_eq_false (fun x => h4 ((Durable.eq_iff d e).1 x).2.2.2.1)]
          iapply HΦ; ipureintro; trivial
      · rw [decide_eq_false h3]
        wp_auto
        rw [decide_eq_false (fun x => h3 ((Durable.eq_iff d e).1 x).2.2.1)]
        iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false (fun x => h2 (hv.1 x))]
      wp_auto
      rw [decide_eq_false (fun x => h2 ((Durable.eq_iff d e).1 x).2.1)]
      iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false (fun x => h1 (ht.1 x))]
    wp_auto
    rw [decide_eq_false (fun x => h1 ((Durable.eq_iff d e).1 x).1)]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
