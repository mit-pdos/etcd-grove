/-
`clientv3.isSafeRetryMutableRPC` (`client/v3/retry.go`).

Users: the retry interceptor (1c: whether a non-repeatable call may be resent).

Proof sketch: `status.FromError`, `rpctypes.ErrorDesc` (2a's specs over `callErr`: a `.notSent` error is a status `Unavailable` with one of the two descriptions, the other kinds have neither).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/isSafeRetryMutableRPC.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `isSafeRetryMutableRPC(err)`: true exactly for an error of a request that never left the
client. -/
def isSafeRetryMutableRPC.spec : Prop :=
  ∀ (err : GoInterface) (k : CallErr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ callErr err k }}
    (App (Val (@! go_etcd_io.etcd.client.v3.isSafeRetryMutableRPC)) (Val #err))
  {{ (b : Bool), RET #b; ⌜b = true ↔ k = .notSent⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
