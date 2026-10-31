/-
Proof of `Spec/go_etcd_io/etcd/client/v3/txn__Then.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.txn__Then
public import Spec.go_etcd_io.etcd.client.v3.Op__isWrite
public import Spec.go_etcd_io.etcd.client.v3.Op__toRequestOp
public import Perennial.Proof.sync.Link

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

theorem txn.Then.wp_proof (wp_isWrite : Op.isWrite.spec (GF := GF) (hG := hG))
    (wp_toRequestOp : Op.toRequestOp.spec (GF := GF) (hG := hG)) :
    txn.Then.spec (GF := GF) (hG := hG) := by
  -- the proof before: git show 91ba4e9267:Proof/go_etcd_io/etcd/client/v3/txn__Then.lean (invoke-size; before it, 51b0f7adad)
  sorry -- txn-nested: prove after freeze

end proof

end EtcdGrove
end Perennial
