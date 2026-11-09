/-
`clientv3.isSafeRetry` (`client/v3/retry_interceptor.go`).

Users: the unary interceptor.

Proof sketch: `isContextError` (its spec): false. The learner's refusal (`errors.Is` with
`rpctypes.ErrGRPCNotSupportedForLearner`, 2a: true exactly for `.etcd .notSupportedForLearner`)
with more than one endpoint (`Endpoints`): true. By the policy: repeatable: `isSafeRetryImmutableRPC`
(W0); non-repeatable: `isSafeRetryMutableRPC` (W0: true iff `.notSent`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/isSafeRetry.lean`.

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

/-- `isSafeRetry(c, err, opts)`: true only for a repeatable call, a not-sent attempt, or a
learner's refusal. -/
def isSafeRetry.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (err : GoInterface) (k : CallErr) (p : Loc)
    (o : RetryOptsM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who ∗ callErr err k ∗ optionsAt p o }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.isSafeRetry)) (Val #c)) (Val #err)) (Val #p))
  {{ (b : Bool), RET #b;
      ⌜b = true → o.rep = true ∨ k = .notSent ∨ k = .etcd .notSupportedForLearner⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
