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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- **`ErrorDesc` over grpc's `status` alone** (prove-rpcmap, 2026-11-20): `ErrorDesc.spec` with
`isPkgInit` of grpc's `status` in place of `rpctypes`' own, which is all the proof uses: for
`rpctypes`' initializer, whose map literal `errStringToError` calls it before the package's
`isPkgInit` holds (`InitLinked.lean`). -/
theorem rpctypes.ErrorDesc.wp_init
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG)) :
    ∀ (err : GoError) (m : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ statusErrOk err ∗
        descIs err m }}
      (App (Val (@! go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrorDesc)) (Val #err))
    {{ RET #m; True }} := by
  intro err m
  wp_start as ⟨#Hok, #Hm⟩
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_auto
  ihave ⟨%cFE, #HcFE⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_code _ $$ Hok
  wp_apply wp_FromError err m cFE $$ [$Hst $Hok $Hm $HcFE] as %s %ok ⟨%Hnil, #HCode, #HMsg, #HErr, %Hng, -⟩
  cases ok
  · wp_auto
    cases err with
    | nil => exact absurd (Hnil rfl) (by simp)
    | ok e =>
      -- (D29) not a status error: its `Error()` returns its description
      have hpe : false = false ∧ GoInterface.ok e = GoInterface.ok e := ⟨rfl, rfl⟩
      ihave #HE := HErr $$ %e %hpe
      wp_apply HE
      iapply HΦ
      itrivial
  · wp_auto
    wp_apply HMsg
    iapply HΦ
    itrivial

theorem rpctypes.ErrorDesc.wp_proof
    (wp_FromError : EtcdGrove.status.FromError.spec (GF := GF) (hG := hG)) :
    rpctypes.ErrorDesc.spec (GF := GF) (hG := hG) := by
  intro err m
  wp_start_folded as ⟨#Hok, #Hm⟩
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  wp_apply rpctypes.ErrorDesc.wp_init wp_FromError err m $$ [$Hst $Hok $Hm]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
