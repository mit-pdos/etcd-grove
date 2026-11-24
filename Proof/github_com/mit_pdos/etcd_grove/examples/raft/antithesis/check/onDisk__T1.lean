/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.T1()` (B 291-359, `OnDisk.T1`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__term
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
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

theorem onDisk.T1.wp_proof (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_term : Event.term.spec (GF := GF) (hG := hG)) :
    onDisk.T1.spec (GF := GF) (hG := hG) := by
  intro g x v
  wp_start as ⟨#Hx, %Hv⟩
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_w_unfold.method_unfold]
  try wp_auto
  wp_apply wp_w g x $$ [Hx] as %e #He
  · iexact Hx
  try wp_auto
  wp_apply wp_term e x.w v $$ [He] as %u %Hu
  · iframe He; ipureintro; exact Hv
  try wp_auto
  iapply HΦ; ipureintro; exact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
