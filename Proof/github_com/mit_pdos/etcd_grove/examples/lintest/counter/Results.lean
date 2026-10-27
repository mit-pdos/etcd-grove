/-
Lean-first (no Rocq counterpart).

# lintest/counter: the results (2026-10-14)

**`Check(CounterClock(), clients, ops, timeout)` never returns `Illegal`** (and returns `Ok` if
`timeout ≤ 0`), under `Run`'s bounds on `clients` and `ops`, for executions of fewer than
`2^63` steps (`receiptBound GF ≤ 2^63`, `CounterClock`'s premise: the clock does not wrap
around), with the clock's invariant at any namespace `N` other than `lintestN`.

- `CheckCounterClock.wp_proof` derives it from `CounterClock.spec` and `Check.spec`, as the
  discipline asks (callee specs as hypotheses).
- `wp_CheckCounterClock` is it with every callee linked: the counter's (`counter/Link.lean`),
  the driver's (`lintest/Link.lean`: `Run`, `runClient`, `CounterClock`) and porcupine's
  (`porcupine/Link.lean`: the whole checker). Its `#print axioms` is the trust base of the
  example, end to end.

Both assume an instance `[NaInvG GF]` (iris-lean's camera of non-atomic invariants, in which
porcupine's `checkSingle` shares the model's state values, `porcupine/Shared.lean`), which
Perennial's `allG` does not provide yet and nothing in this repository provides: until it does,
the result is conditional on that instance (`notes/STATUS.md`, "Porcupine").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Model
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.New
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Counter__Apply
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]
-- porcupine's camera of non-atomic invariants, not yet in Perennial's `allG` (see the header)
variable [NaInvG GF]

/-- `Check(lintest.CounterClock(), clients, ops, timeout)` (see the file header). -/
abbrev CheckCounterClock.spec : Prop :=
  ∀ (N : Namespace) (clients ops dur : w64),
  receiptBound GF ≤ 2 ^ 63 → (↑lintestN : CoPset) ⊆ ⊤ \ ↑N →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter ∗
      context.isClosedchanInit }}
    (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.counter.Check))
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock)) (Val #())))
      (Val #clients)) (Val #ops)) (Val #dur))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

theorem CheckCounterClock.wp_proof
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    CheckCounterClock.spec (GF := GF) (hG := hG) := by
  intro N clients ops dur Hbound HN H0 H31 Hops Hmul
  iintro %Φ ⟨#Hpkg, #Hcc⟩ HΦ
  wp_apply wp_CounterClock N Hbound as %f ⟨%clockVal, #Hclk, Ht0⟩
  wp_apply wp_Check clockVal (W64 0) ↑N f clients ops dur HN H0 H31 Hops Hmul $$ [Ht0]
    as %r %Hr
  · iframe
    iframe #
  iapply HΦ
  ipureintro
  exact Hr

/-- **The closed result**: `CheckCounterClock.spec`, with every callee linked (the counter's,
the driver's and porcupine's proofs, `Link.lean`). -/
theorem wp_CheckCounterClock : CheckCounterClock.spec (GF := GF) (hG := hG) :=
  CheckCounterClock.wp_proof lintest.wp_CounterClock counter.wp_Check

end results

end counter
end lintest
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.lintest.counter.wp_CheckCounterClock
