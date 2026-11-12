/-
Proof of `Spec/go_etcd_io/etcd/client/v3/isContextError.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.isContextError
public import Spec.google_golang_org.grpc.status.Code

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem isContextError.wp_proof
    (wp_Code : status.Code.spec (GF := GF) (hG := hG)) :
    isContextError.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hse
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Code err $$ [$Hst $Hse] as %c1 -
  wp_if_destruct
  · iapply HΦ; itrivial
  · wp_apply wp_Code err $$ [$Hst $Hse] as %c2 -
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
