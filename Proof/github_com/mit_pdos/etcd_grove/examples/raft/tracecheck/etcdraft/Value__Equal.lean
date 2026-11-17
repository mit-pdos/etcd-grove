/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Value__Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Value__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section pure

/-- A value's kind tag (the Go's `ValueKind`). -/
def Value.kindW : Value → w8
  | .val _ => W8 0 | .emptySeq => W8 1 | .conf _ _ => W8 2

/-- A value's `Val` (0 but for a client value's). -/
def Value.valZ : Value → Int
  | .val n => n | _ => 0

/-- A value's `NewConf` (empty but for a configuration's). -/
def Value.ncS : Value → SetIds
  | .conf nc _ => nc | _ => []

/-- A value's `Learners` (empty but for a configuration's). -/
def Value.lnS : Value → SetIds
  | .conf _ ln => ln | _ => []

/-- Two values are equal when their four fields are. -/
theorem Value.eq_iff_fields (a b : Value) :
    a = b ↔ (a.kindW = b.kindW ∧ a.valZ = b.valZ ∧ a.ncS = b.ncS ∧ a.lnS = b.lnS) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases a <;> cases b <;> simp [Value.kindW, Value.valZ, Value.ncS, Value.lnS]

end pure

section fields
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `valueRO`, field by field. -/
theorem valueRO_fields (v : G.Value) (a : Value) :
    valueRO (GF := GF) v a ⊢ iprop(⌜v.Kind' = a.kindW ∧ sint.Z v.Val' = a.valZ⌝ ∗
      setRO v.NewConf' a.ncS ∗ setRO v.Learners' a.lnS) := by
  cases a <;> unfold valueRO
  · iintro ⟨%H, Hn, Hl⟩; iframe; ipureintro; exact H
  · iintro ⟨%H, Hn, Hl⟩; iframe; ipureintro; refine ⟨H.1, ?_⟩; rw [H.2]; rfl
  · iintro ⟨%H, Hn, Hl⟩; iframe; ipureintro; refine ⟨H.1, ?_⟩; rw [H.2]; rfl

end fields

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Value.Equal.wp_proof (wp_SetEqual : Set.Equal.spec (GF := GF) (hG := hG)) :
    Value.Equal.spec (GF := GF) (hG := hG) := by
  intro v a w b
  wp_start as ⟨#Hv, #Hw⟩
  ihave ⟨%Hv1, #Hvn, #Hvl⟩ := valueRO_fields $$ Hv
  ihave ⟨%Hw1, #Hwn, #Hwl⟩ := valueRO_fields $$ Hw
  wp_auto
  have Hab := Value.eq_iff_fields a b
  have hvz : ∀ x y : w64, x = y ↔ sint.Z x = sint.Z y := fun x y =>
    ⟨fun h => h ▸ rfl, fun h => by word⟩
  by_cases hk : v.Kind' = w.Kind'
  · rw [decide_eq_true hk]
    wp_auto
    by_cases hval : v.Val' = w.Val'
    · rw [decide_eq_true hval]
      wp_auto
      icases typedPointsto_split _ _ _ $$ v with Hvf
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hvf
      rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
      try wp_auto
      wp_apply wp_SetEqual _ _ _ _ $$ [Hvn Hwn] as -
      · iframe Hvn Hwn
      by_cases hnc : a.ncS = b.ncS
      · rw [decide_eq_true hnc]
        wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
        try wp_auto
        wp_apply wp_SetEqual _ _ _ _ $$ [Hvl Hwl] as -
        · iframe Hvl Hwl
        try wp_auto
        have : decide (a = b) = decide (a.lnS = b.lnS) := by
          apply decide_eq_decide.2
          rw [Hab]
          refine ⟨fun h => h.2.2.2, fun h => ⟨?_, ?_, hnc, h⟩⟩
          · rw [← Hv1.1, ← Hw1.1, hk]
          · rw [← Hv1.2, ← Hw1.2, hval]
        rw [this]
        iapply HΦ; ipureintro; trivial
      · rw [decide_eq_false hnc]
        wp_auto
        rw [decide_eq_false (fun h => hnc (Hab.1 h).2.2.1)]
        iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false hval]
      wp_auto
      rw [decide_eq_false (fun h => hval ((hvz _ _).2 (by rw [Hv1.2, Hw1.2, ((Hab.1 h).2.1)])))]
      iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false hk]
    wp_auto
    rw [decide_eq_false (fun h => hk (by rw [Hv1.1, Hw1.1, (Hab.1 h).1]))]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
