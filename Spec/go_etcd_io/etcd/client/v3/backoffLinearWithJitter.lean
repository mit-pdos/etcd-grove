/-
`backoffLinearWithJitter(waitBetween, jitterFraction)` (`client/v3/retry_interceptor.go`; the
backoff of `defaultOptions`, prove-ps2-rqb, 2026-11-22). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open go_etcd_io.etcd.cache.v3 (backoffOk)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `backoffLinearWithJitter(w, j)`: a backoff function that returns (`backoffOk`). No premise (it
runs in the package's own initializer, `defaultOptions`). -/
abbrev backoffLinearWithJitter.spec : Prop :=
  ∀ (w : time.Duration) (j : w64),
  {{ (True : IProp GF) }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.backoffLinearWithJitter)) (Val #w)) (Val #j))
  {{ (bf : GoFunc), RET #bf; backoffOk bf }}

end spec

end EtcdGrove
end Perennial
