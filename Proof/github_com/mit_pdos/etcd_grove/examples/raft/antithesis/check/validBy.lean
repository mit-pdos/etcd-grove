/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `validBy` (B 232-233).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.validBy

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

theorem validBy.wp_proof : validBy.spec (GF := GF) (hG := hG) := by
  intro t
  generalize hb : ([go!"recv", go!"tick", go!"campaign", go!"propose", go!"write", go!"apply", go!"boot", go!"transfer", go!"snapstatus", go!"read"] : List Str).contains t = b
  wp_start as #_
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals (cases b)
  all_goals (first | (iapply HΦ; ipureintro; trivial) | (exfalso; simp_all; done))

end proof

end AntCheck
end EtcdGrove
end Perennial
