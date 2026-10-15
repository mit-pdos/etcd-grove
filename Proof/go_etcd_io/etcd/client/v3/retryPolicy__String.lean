/-
Proof of `Spec/go_etcd_io/etcd/client/v3/retryPolicy__String.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.retryPolicy__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem retryPolicy.String.wp_proof :
    retryPolicy.String.spec (GF := GF) (hG := hG) := by
  intro rp
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ; itrivial
  wp_if_destruct
  · iapply HΦ; itrivial
  · iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
