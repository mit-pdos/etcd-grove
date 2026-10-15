/- Lean-first (no Rocq counterpart).

`CounterClock()` (lintest.go): a logical clock, `t.Add(1)` on a fresh `atomic.Int64`. It
returns a clock (`clockSpec`, `Proof/.../lintest/Defs.lean`) over a fresh ghost value, starting
at `0`, whose invariant is at the caller's namespace `N`.

The counter is incremented once per reading, so it would wrap around after `2^63 - 1`
readings, and a reading would then be smaller than the one before. The premise
`receiptBound GF ≤ 2 ^ 63` (time receipts, Perennial's `GooseLang/Receipts.lean`) rules that
out: every reading takes a Go step, and an execution of fewer than `receiptBound GF` steps
makes fewer than `2^63 - 1` readings. A client discharges it at adequacy time, for
executions of fewer than `2^63` steps.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

/-- See the file header. -/
abbrev CounterClock.spec : Prop :=
  ∀ (N : Namespace), receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock)) (Val #()))
  {{ (f : GoFunc), RET #f;
      ∃ clockVal : w64 → IProp GF, clockSpec clockVal (↑N) f ∗ clockVal (W64 0) }}

end spec

end lintest
end EtcdGrove
end Perennial
