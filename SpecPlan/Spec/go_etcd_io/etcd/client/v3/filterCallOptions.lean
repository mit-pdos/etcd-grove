/-
`clientv3.filterCallOptions` (`client/v3/retry_interceptor.go`).

Users: the interceptors.

Proof sketch: a type switch per option (`retryOption` or not), two fresh slices by `append` onto
`nil` (`callOptsOk`'s realization: its options are the client's gRPC ones and retry options).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/filterCallOptions.lean`.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `filterCallOptions(opts)`: the gRPC options, and the retry options (the policy repeatable iff
`rep`; a limit only `0`). -/
def filterCallOptions.spec : Prop :=
  ∀ (sl : GoSlice) (rep : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ callOptsOk sl rep }}
    (App (Val (@! go_etcd_io.etcd.client.v3.filterCallOptions)) (Val #sl))
  {{ (g r : GoSlice), RET (PairV #g #r); grpcCallOptsOk g ∗ ∃ fs, retryOptsAt r fs ∗
      ⌜∀ o, (applyRetry fs o).rep = (o.rep || rep) ∧
        ((applyRetry fs o).max = o.max ∨ (applyRetry fs o).max = W64 0)⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
