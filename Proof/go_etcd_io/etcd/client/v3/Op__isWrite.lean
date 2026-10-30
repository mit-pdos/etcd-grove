/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__isWrite.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__isWrite

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Op.isWrite.wp_proof : Op.isWrite.spec (GF := GF) (hG := hG) := by
  -- the proof before: git show 51b0f7adad:Proof/go_etcd_io/etcd/client/v3/Op__isWrite.lean
  sorry -- txn-nested: prove after freeze

end proof

end EtcdGrove
end Perennial
