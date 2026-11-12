/-
`clientv3.jitterUp` (`client/v3/utils.go`).

Users: the retry interceptor's backoff (1c: `waitRetryBackoff`, `backoffLinearWithJitter`).

Proof sketch: floating-point arithmetic and `rand.Float64` (Perennial's `math/rand`); no panic.

Changes: none (no old spec): added for the users named above.

Margin: the result is within the jitter fraction of `duration`; not stated (no user relies on it for safety).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `jitterUp(duration, jitter)`: some duration. -/
def jitterUp.spec : Prop :=
  ∀ (d : w64) (j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.jitterUp)) (Val #d)) (Val #j))
  {{ (r : w64), RET #r; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial
