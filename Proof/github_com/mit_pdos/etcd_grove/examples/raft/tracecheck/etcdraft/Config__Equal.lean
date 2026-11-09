/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Config__Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Config__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Equal

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

/-- `Config`'s equality, field by field. -/
theorem Config.eq_iff (c d : Config) :
    c = d ↔ c.incoming = d.incoming ∧ c.outgoing = d.outgoing ∧ c.learners = d.learners := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩; cases c; cases d; simp_all

theorem Config.Equal.wp_proof (wp_SetEqual : Set.Equal.spec (GF := GF) (hG := hG)) :
    Config.Equal.spec (GF := GF) (hG := hG) := by
  intro g c h d
  wp_start as ⟨#Hc, #Hd⟩
  iunfold configRO at Hc Hd
  icases Hc with ⟨%a, %b, %Hab, #Ha, #Hb, #Hl⟩
  icases Hd with ⟨%a', %b', %Hab', #Ha', #Hb', #Hl'⟩
  wp_auto
  ipersist c
  ipersist d
  icases typedPointsto_split _ _ _ $$ c with Hcf
  icases typedPointsto_split _ _ _ $$ d with Hdf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hcf with ⟨#Jc, #Lc, -⟩
  icases Hdf with ⟨#Jd, #Ld, -⟩
  icases array_acc _ 0 _ _ _ a (Int.le_refl _) (by rw [Hab]; rfl) $$ Jc with ⟨#Hc0, -⟩
  icases array_acc _ 1 _ _ _ b (by decide) (by rw [Hab]; rfl) $$ Jc with ⟨#Hc1, -⟩
  icases array_acc _ 0 _ _ _ a' (Int.le_refl _) (by rw [Hab']; rfl) $$ Jd with ⟨#Hd0, -⟩
  icases array_acc _ 1 _ _ _ b' (by decide) (by rw [Hab']; rfl) $$ Jd with ⟨#Hd1, -⟩
  rw [show sint.Z (W64 0) = 0 from rfl]
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
  rw [show sint.Z (W64 0) = 0 from rfl]
  wp_auto
  wp_apply wp_SetEqual _ _ _ _ $$ [Ha Ha'] as -
  · iframe Ha Ha'
  by_cases h0 : c.incoming = d.incoming
  · rw [decide_eq_true h0]
    wp_auto
    rw [show sint.Z (W64 1) = 1 from rfl]
    wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
    rw [show sint.Z (W64 1) = 1 from rfl]
    wp_auto
    wp_apply wp_SetEqual _ _ _ _ $$ [Hb Hb'] as -
    · iframe Hb Hb'
    by_cases h1 : c.outgoing = d.outgoing
    · rw [decide_eq_true h1]
      wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
      wp_auto
      wp_apply wp_SetEqual _ _ _ _ $$ [Hl Hl'] as -
      · iframe Hl Hl'
      try wp_auto
      have : decide (c.learners = d.learners) = decide (c = d) := by
        apply decide_eq_decide.2; rw [Config.eq_iff]; simp [h0, h1]
      rw [this]
      iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false h1]
      wp_auto
      rw [decide_eq_false (fun e => h1 ((Config.eq_iff c d).1 e).2.1)]
      iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false h0]
    wp_auto
    rw [decide_eq_false (fun e => h0 ((Config.eq_iff c d).1 e).1)]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
