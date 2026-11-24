/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `SameConf` (B 142-143).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SameConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__voters
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__outgoing
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Equal
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

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

theorem SameConf.wp_proof (wp_has : Event.has.spec (GF := GF) (hG := hG))
    (wp_voters : Event.voters.spec (GF := GF) (hG := hG))
    (wp_outgoing : Event.outgoing.spec (GF := GF) (hG := hG))
    (wp_SetOf : SetOf.spec (GF := GF) (hG := hG))
    (wp_Equal : Set.Equal.spec (GF := GF) (hG := hG)) :
    SameConf.spec (GF := GF) (hG := hG) := by
  intro e ev g c b
  wp_start as ⟨#He, #Hc, %Hb⟩
  obtain ⟨Hb, Hsz⟩ := Hb
  iunfold confRO at Hc
  icases Hc with ⟨#Hin, #Hout⟩
  unfold sameConf at Hb
  wp_auto
  rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FVoters : val) = #fVoters from rfl]
  wp_apply wp_has e ev fVoters ev.voters.isSome $$ [He]
  · iframe He; ipureintro; exact Event.hasF_Voters ev
  cases hv : ev.voters with
  | none =>
    rw [hv] at Hb; cases Hb
    simp only [Option.isSome_none, Bool.not_false]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  | some v =>
    rw [hv] at Hb
    obtain ⟨x, hx, ht, hf⟩ := andM_ok Hb
    cases hx
    simp only [Option.isSome_some, Bool.not_true]
    have hvl : (v.length : Int) < 2 ^ 62 := by
      have : v.length ≤ ev.size := by unfold Event.size; rw [hv]; simp; omega
      omega
    try wp_auto
    wp_apply wp_voters e ev v $$ [He] as %vs #Hvs
    · iframe He; ipureintro; rw [hv]; rfl
    try wp_auto
    wp_apply wp_SetOf vs v $$ [Hvs] as %sv #Hsv
    · iframe Hvs; ipureintro; exact hvl
    try wp_auto
    wp_apply wp_Equal sv (setOf v) g.In' c.cin $$ [Hsv Hin]
    · iframe Hsv Hin
    by_cases hin : setOf v = c.cin
    · rw [decide_eq_true hin]
      have hb' := ht (by simp [hin])
      cases ho : ev.outgoing with
      | none => rw [ho] at hb'; cases hb'
      | some o =>
      rw [ho] at hb'
      simp only [need, ok_bind, pure_ok] at hb'
      cases hb'
      have hol : (o.length : Int) < 2 ^ 62 := by
        have : o.length ≤ ev.size := by unfold Event.size; rw [ho]; simp
        omega
      try wp_auto
      wp_apply wp_outgoing e ev o $$ [He] as %os #Hos
      · iframe He; ipureintro; rw [ho]; rfl
      try wp_auto
      wp_apply wp_SetOf os o $$ [Hos] as %so #Hso
      · iframe Hos; ipureintro; exact hol
      try wp_auto
      wp_apply wp_Equal so (setOf o) g.Out' c.cout $$ [Hso Hout]
      · iframe Hso Hout
      try wp_auto
      have : decide (setOf o = c.cout) = (setOf o == c.cout) := by
        by_cases h : setOf o = c.cout <;> simp [h]
      rw [this]
      iapply HΦ; ipureintro; trivial
    · rw [decide_eq_false hin]
      have hb' := hf (by simp [hin])
      subst hb'
      try wp_auto
      iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
