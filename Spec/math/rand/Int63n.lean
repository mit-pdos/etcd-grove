/-
`rand.Int63n`, of Go's `math/rand` (names-only in Perennial): the trust boundary. Lean-first (no
Rocq counterpart); the watch slice's unit W-S (2026-10-14: `GetProgressReportInterval`'s jitter).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `rand.Int63n(n)` of a positive `n`: a number in `[0, n)` (Go panics for `n <= 0`). -/
abbrev rand.Int63n.spec : Prop :=
  ∀ n : w64,
  {{ (⌜0 < sint.Z n⌝ : IProp GF) }}
    (App (Val (@! _root_.Perennial.math.rand.Int63n)) (Val #n))
  {{ (x : w64), RET #x; ⌜0 ≤ sint.Z x ∧ sint.Z x < sint.Z n⌝ }}

end spec

end EtcdGrove
end Perennial
