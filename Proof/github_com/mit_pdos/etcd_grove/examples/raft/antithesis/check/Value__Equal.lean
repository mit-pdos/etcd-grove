/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): the proof of `Value.Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.stringsEqual

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- `==` is `decide (· = ·)` under a lawful `BEq`. -/
theorem beq_dec {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (a b : α) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem Value.Equal.wp_proof (wp_stringsEqual : stringsEqual.spec (GF := GF) (hG := hG)) :
    Value.Equal.spec (GF := GF) (hG := hG) := by
  intro g v h w b
  wp_start as ⟨#Hv, #Hw, %Hb⟩
  iunfold valueRO at Hv Hw
  icases Hv with ⟨%Hv1, #Hva, #Hvr⟩
  icases Hw with ⟨%Hw1, #Hwa, #Hwr⟩
  obtain ⟨hvr, hvs, hvj, hvl⟩ := Hv1
  obtain ⟨hwr, hws, hwj, hwl⟩ := Hw1
  unfold Value.equal at Hb
  have hrec : v.isRec = w.isRec := by
    by_cases hne : v.isRec = w.isRec
    · exact hne
    · rw [ite_eq_left hne] at Hb; cases Hb
  rw [ite_eq_right (by simpa using hrec)] at Hb
  have hrec' : g.IsRec' = h.IsRec' := by rw [hvr, hwr, hrec]
  wp_auto
  rw [decide_eq_true hrec']
  wp_auto
  icases typedPointsto_split _ _ _ $$ v with Hvf
  icases typedPointsto_split _ _ _ $$ w with Hwf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hvf
  iNamed Hwf
  try wp_auto
  cases hg : g.IsRec'
  · -- strings
    try wp_auto
    rw [ite_eq_left (by rw [← hvr, hg]; rfl)] at Hb
    cases Hb
    have : (v.str == w.str) = decide (g.Str' = h.Str') := by rw [hvs, hws]; exact beq_dec v.str w.str
    rw [this]
    iapply HΦ; ipureintro; trivial
  · try wp_auto
    rw [ite_eq_right (by rw [← hvr, hg]; decide)] at Hb
    cases Hb
    wp_apply wp_stringsEqual _ _ _ _ $$ [Hva Hwa] as -
    · iframe Hva Hwa
    by_cases ha : v.add = w.add
    · rw [decide_eq_true ha]
      try wp_auto
      wp_apply wp_stringsEqual _ _ _ _ $$ [Hvr Hwr] as -
      · iframe Hvr Hwr
      by_cases hr : v.remove = w.remove
      · rw [decide_eq_true hr]
        try wp_auto
        by_cases hj : g.Joint' = h.Joint'
        · rw [decide_eq_true hj]
          try wp_auto
          have e : (v.add == w.add && v.remove == w.remove && v.joint == w.joint && v.leave == w.leave) =
              decide (g.Leave' = h.Leave') := by
            rw [beq_dec, beq_dec, beq_dec, beq_dec, decide_eq_true ha, decide_eq_true hr,
              decide_eq_true (show v.joint = w.joint by rw [← hvj, ← hwj, hj]), hvl, hwl]
            simp
          rw [e]
          iapply HΦ; ipureintro; trivial
        · rw [decide_eq_false hj]
          try wp_auto
          have e : (v.add == w.add && v.remove == w.remove && v.joint == w.joint && v.leave == w.leave) =
              false := by
            rw [beq_dec v.joint, decide_eq_false (show ¬ v.joint = w.joint by rw [← hvj, ← hwj]; exact hj)]
            simp
          rw [e]
          iapply HΦ; ipureintro; trivial
      · rw [decide_eq_false hr]
        try wp_auto
        have e : (v.add == w.add && v.remove == w.remove && v.joint == w.joint && v.leave == w.leave) =
            false := by
          rw [beq_dec v.remove, decide_eq_false hr]; simp
        rw [e]
        iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false ha]
      try wp_auto
      have e : (v.add == w.add && v.remove == w.remove && v.joint == w.joint && v.leave == w.leave) =
          false := by
        rw [beq_dec v.add, decide_eq_false ha]; simp
      rw [e]
      iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
