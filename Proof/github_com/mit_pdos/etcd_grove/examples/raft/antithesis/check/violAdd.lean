/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `violAdd`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.violAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SetAdd

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

theorem violAdd.wp_proof (wp_SetAdd : SetAdd.spec (GF := GF) (hG := hG)) :
    violAdd.spec (GF := GF) (hG := hG) := by
  intro sl xs x
  wp_start as ⟨#Hs, %Hlen⟩
  wp_auto
  wp_apply wp_SetAdd sl xs x $$ [Hs] as %u #Hu
  · iframe Hs; ipureintro; exact Hlen
  try wp_auto
  iapply HΦ; iexact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
