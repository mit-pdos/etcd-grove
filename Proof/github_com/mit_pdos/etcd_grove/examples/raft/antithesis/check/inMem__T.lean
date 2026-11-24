/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.T()` (B 214-230, `InMem.T`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__T
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
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem inMem.T.wp_proof
    (wp_term : Event.term.spec (GF := GF) (hG := hG)) :
    inMem.T.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  wp_auto
  wp_apply wp_term gx.ev' x.ev v $$ [He] as %u %Hu
  · iframe He; ipureintro; exact Hv
  try wp_auto
  iapply HΦ; ipureintro; exact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
