/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.clone`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone

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

theorem State.clone.wp_proof : State.clone.spec (GF := GF) (hG := hG) := by
  intro p s
  wp_start as #Hs
  iunfold stateRO at Hs
  icases Hs with ⟨%g, #Hp, #Hf⟩
  wp_auto
  iapply HΦ
  iunfold stateOwn
  iexists g
  iframe
  iexact Hf

end proof

end AntCheck
end EtcdGrove
end Perennial
