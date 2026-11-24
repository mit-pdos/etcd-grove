/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Msg.need`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__need

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

theorem Msg.need.wp_proof : Msg.need.spec (GF := GF) (hG := hG) := by
  intro g f
  wp_start as %Hb
  wp_auto
  wp_if_destruct
  · exact absurd (by assumption) Hb
  iapply HΦ
  ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
