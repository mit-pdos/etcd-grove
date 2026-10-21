/-
`filterCallOptions(opts)` (`client/v3/retry_interceptor.go`; unit P3a). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk backoffOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `filterCallOptions(opts)` of the client's call options (`callOptsOk`) splits them: grpc's
(each holding only scalars; a fresh slice, owned with its capacity) and the `retryOption`s (each
writing only `retryPolicy`, `retryApplyOk`; a fresh slice). -/
abbrev filterCallOptions.spec : Prop :=
  ∀ (sl : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ sl ↦*□ vs ∗ callOptsOk vs }}
    (App (Val (@! go_etcd_io.etcd.client.v3.filterCallOptions)) (Val #sl))
  {{ (g r : GoSlice), RET (PairV #g #r);
      ∃ (gs : List GoInterface) (ros : List go_etcd_io.etcd.client.v3.retryOption),
        g ↦* gs ∗ ownSliceCap GoInterface g (DFrac.own 1) ∗
        ⌜∀ v ∈ gs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧ t ∈ grpcScalarOptTys⌝ ∗
        r ↦* ros ∗ ([∗list] ro ∈ ros, retryApplyOk ro.applyFunc') ∗
        -- (2026-10-21, D29) scalar options only: no retry options
        ⌜(∀ v ∈ vs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧
          t ∈ grpcScalarOptTys) → ros = []⌝ }}

end spec

end EtcdGrove
end Perennial
