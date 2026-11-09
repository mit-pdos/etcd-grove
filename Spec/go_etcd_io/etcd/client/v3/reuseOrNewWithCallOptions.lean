/-
`clientv3.reuseOrNewWithCallOptions` (`client/v3/retry_interceptor.go`).

Users: the interceptors.

Proof sketch: no option: the same pointer. Else a fresh copy, each option's closure applied in
order (`retryOptAt`), persisted.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/reuseOrNewWithCallOptions.lean`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `reuseOrNewWithCallOptions(p, fs)`: the options with `fs` applied. -/
def reuseOrNewWithCallOptions.spec : Prop :=
  ∀ (p : Loc) (o : RetryOptsM) (sl : GoSlice) (fs : List (RetryOptsM → RetryOptsM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optionsAt p o ∗ retryOptsAt sl fs }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.reuseOrNewWithCallOptions)) (Val #p)) (Val #sl))
  {{ (p' : Loc), RET #p'; optionsAt p' (applyRetry fs o) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
