/-
Proof of `Spec/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/ErrorDesc.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc
public import Spec.google_golang_org.grpc.status.FromError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

theorem rpctypes.ErrorDesc.wp_proof
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG)) :
    rpctypes.ErrorDesc.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hok
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_FromError err $$ [$Hst $Hok] as %s %ok ⟨%Hnil, #HCode, #HMsg⟩
  cases ok
  · wp_auto
    cases err with
    | nil => exact absurd (Hnil rfl) (by simp)
    | ok e =>
      iunfold statusErrOk at Hok
      ihave ⟨#HE, -⟩ := Hok $$ %e %rfl
      iunfold errorStringSpec at HE
      wp_apply HE as %str
      iapply HΦ
      itrivial
  · wp_auto
    wp_apply HMsg as %msg
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
