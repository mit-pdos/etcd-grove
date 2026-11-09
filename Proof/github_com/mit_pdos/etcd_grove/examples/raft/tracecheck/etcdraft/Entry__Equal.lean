/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Entry__Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Entry__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Value__Equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

/-- The Go's entry types are distinct. -/
theorem entryTypeW_inj (s t : EntryType)
    (h : (match s with | .value => W8 0 | .config => W8 1 : w8) =
      (match t with | .value => W8 0 | .config => W8 1)) : s = t := by
  cases s <;> cases t <;> first | rfl | exact absurd h (by decide)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Entry.Equal.wp_proof (wp_ValueEqual : Value.Equal.spec (GF := GF) (hG := hG)) :
    Entry.Equal.spec (GF := GF) (hG := hG) := by
  intro e x f y
  wp_start as ⟨#He, #Hf⟩
  iunfold entryRO at He Hf
  icases He with ⟨%He1, #Hev⟩
  icases Hf with ⟨%Hf1, #Hfv⟩
  wp_auto
  by_cases ht : e.Term' = f.Term'
  · rw [decide_eq_true ht]
    wp_auto
    by_cases hty : e.Type' = f.Type'
    · rw [decide_eq_true hty]
      wp_auto
      icases typedPointsto_split _ _ _ $$ e with Hef
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hef
      rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Value.TypeAssumptions.ptr_Equal_unfold.method_unfold]
      try wp_auto
      wp_apply wp_ValueEqual _ _ _ _ $$ [Hev Hfv] as -
      · iframe Hev Hfv
      try wp_auto
      have : decide (x = y) = decide (x.value = y.value) := by
        apply decide_eq_decide.2
        constructor
        · rintro rfl; rfl
        · intro hv
          have h1 : x.term = y.term := by rw [← He1.1, ← Hf1.1, ht]
          have h2 : x.type = y.type := by
            have h := He1.2.symm.trans (hty.trans Hf1.2)
            exact entryTypeW_inj _ _ h
          cases x; cases y; simp_all
      rw [this]
      iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false hty]
      wp_auto
      rw [decide_eq_false (fun h => hty (by subst h; rw [He1.2, Hf1.2]))]
      iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false ht]
    wp_auto
    rw [decide_eq_false (fun h => ht (by
      have : sint.Z e.Term' = sint.Z f.Term' := by rw [He1.1, Hf1.1, h]
      word))]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
