/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.role1()` (B 214-230, `InMem.role1`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__role1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__role
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem inMem.role1.wp_proof
    (wp_role : Event.role.spec (GF := GF) (hG := hG)) :
    inMem.role1.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  wp_auto
  unfold InMem.role1 at Hv
  obtain ⟨r, hr, Hv⟩ := bind_ok Hv
  simp only [pure_ok, Except.ok.injEq] at Hv
  subst Hv
  wp_apply wp_role gx.ev' x.ev r $$ [He]
  · iframe He; ipureintro; exact hr
  try wp_auto
  by_cases h : r = go!"precandidate"
  · rw [decide_eq_true h]
    rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Follower : val) = #follower from rfl]
    try wp_auto
    rw [beq_of_eq' h]; simp only [ite_true]
    iapply HΦ; ipureintro; trivial
  · rw [decide_eq_false h]
    try wp_auto
    wp_apply wp_role gx.ev' x.ev r $$ [He]
    · iframe He; ipureintro; exact hr
    try wp_auto
    rw [beq_of_ne' h]; simp only [Bool.false_eq_true, ite_false]
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
