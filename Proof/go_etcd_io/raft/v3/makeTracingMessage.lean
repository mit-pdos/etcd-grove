/-
Lean-first (no Rocq counterpart): the proof of `makeTracingMessage`
(`Spec/go_etcd_io/raft/v3/makeTracingMessage.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.makeTracingMessage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem makeTracingMessage.wp_proof :
    makeTracingMessage.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
