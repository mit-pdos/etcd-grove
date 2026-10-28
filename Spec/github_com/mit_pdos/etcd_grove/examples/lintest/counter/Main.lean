/- Lean-first (no Rocq counterpart).

`Main()` (counter.go): `Check(lintest.CounterClock(), 4, 10, 0)`, then a panic unless the
result is `porcupine.Ok`. It returns (never panics) for executions of fewer than `2^63` steps
(`receiptBound GF ≤ 2^63`, `CounterClock`'s premise: the clock does not wrap around), given
`context`'s `isClosedchanInit` (which porcupine's `WithCancel(Background())` needs and
`isPkgInit` does not give; the adequacy theorem gets it from the program's initialization,
`counter/Init.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter ∗
      context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.counter.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end counter
end lintest
end EtcdGrove
end Perennial
