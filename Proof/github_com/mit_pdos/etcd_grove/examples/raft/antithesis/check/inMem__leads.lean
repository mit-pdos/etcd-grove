/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.leads()` (B 214-230, `InMem.leads`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__leads
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

theorem inMem.leads.wp_proof
    (wp_role : Event.role.spec (GF := GF) (hG := hG)) :
    inMem.leads.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  wp_auto
  unfold InMem.leads at Hv
  obtain ⟨y, hy, rfl⟩ := fieldEq_ok Hv
  wp_apply wp_role gx.ev' x.ev y $$ [He]
  · iframe He; ipureintro; exact hy
  try wp_auto
  rw [decide_eq_beq']
  unfold leader
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
