/-
`jitterUp(duration, jitter)` (`client/v3/utils.go`): the backoff's jitter (prove-ps2-rqb,
2026-11-22). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `jitterUp(d, j)` returns (some `Duration`: float arithmetic over `rand.Float64()`, converted back
to an integer). No premise: the backoff functions built from it run outside any package fact. -/
abbrev jitterUp.spec : Prop :=
  ∀ (d : time.Duration) (j : w64),
  {{ (True : IProp GF) }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.jitterUp)) (Val #d)) (Val #j))
  {{ (r : time.Duration), RET #r; True }}

end spec

end EtcdGrove
end Perennial
