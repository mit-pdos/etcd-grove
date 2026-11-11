/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 2) (2026-11-11).

`below(n)` (`examples/raft/tracecheck/concurrent.go`): a random number in `[0, n)`, for `n > 0`
(`primitive.RandomUint64() % uint64(n)`: `n = 0` divides by zero).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- See the file header. -/
abbrev below.spec : Prop :=
  ∀ (n : w64), 0 < sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.below)) (Val #n))
  {{ (r : w64), RET #r; ⌜0 ≤ sint.Z r ∧ sint.Z r < sint.Z n⌝ }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
