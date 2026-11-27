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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `filterCallOptions(opts)` of call options each holding only scalars or a `retryOption` whose
closure meets `A` (persistent; `callOptOkA`: the unary interceptor's, `callOptsOk`, at `retryApplyOk`;
the stream interceptor's at `optApplyKeep · false`) splits them: grpc's (each holding only scalars; a
fresh slice, owned with its capacity) and the `retryOption`s (each meeting `A`; a fresh slice).
(phase7-s3-interceptor, 2026-11-26: generalized from `callOptsOk vs` and `retryApplyOk`, its
instance.) -/
abbrev filterCallOptions.spec : Prop :=
  ∀ (sl : GoSlice) (vs : List GoInterface) (A : GoFunc → IProp GF), (∀ f, Persistent (A f)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ sl ↦*□ vs ∗
      [∗list] v ∈ vs, callOptOkA A v }}
    (App (Val (@! go_etcd_io.etcd.client.v3.filterCallOptions)) (Val #sl))
  {{ (g r : GoSlice), RET (PairV #g #r);
      ∃ (gs : List GoInterface) (ros : List go_etcd_io.etcd.client.v3.retryOption),
        g ↦* gs ∗ ownSliceCap GoInterface g (DFrac.own 1) ∗
        ⌜∀ v ∈ gs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧ t ∈ grpcScalarOptTys⌝ ∗
        r ↦* ros ∗ ([∗list] ro ∈ ros, A ro.applyFunc') ∗
        -- (2026-10-21, D29) scalar options only: no retry options
        ⌜(∀ v ∈ vs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧
          t ∈ grpcScalarOptTys) → ros = []⌝ }}

end spec

end EtcdGrove
end Perennial
