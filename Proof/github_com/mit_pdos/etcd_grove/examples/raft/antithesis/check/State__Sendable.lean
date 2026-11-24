/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `State.Sendable` (B 128).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Sendable
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SendableIn
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

theorem State.Sendable.wp_proof (wp_SendableIn : SendableIn.spec (GF := GF) (hG := hG)) :
    State.Sendable.spec (GF := GF) (hG := hG) := by
  intro p s g f b
  wp_start as ⟨#Hs, #Hf, %Hb⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  wp_auto
  wp_apply wp_SendableIn g.Leaders' s.leaders g.LedLog' s.ledLog g.Chain' s.chain g.TermLen' s.termLen _ f b
    $$ [HLeaders HLedLog HChain HTermLen Hf]
  · iframe HLeaders HLedLog HChain HTermLen Hf; ipureintro; exact Hb
  try wp_auto
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
