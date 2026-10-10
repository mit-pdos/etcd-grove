/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Op__Txn.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Op__Txn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode 

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Op.Txn.wp_proof : Op.Txn.spec (GF := GF) (hG := hG) := by
  intro opp op dq
  wp_start as Hop
  wp_auto
  wp_method_call
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
