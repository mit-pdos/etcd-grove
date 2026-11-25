/- Lean-first (no Rocq counterpart).

# lintest: the step bound of the examples' top-level statements

The examples' `Main`s trace their clients with `lintest.CounterClock()`, an `atomic.Int64`
incremented once per reading. Its spec (`Spec/.../lintest/CounterClock.lean`) takes
`receiptBound GF ≤ 2^63`, time receipts bounding the increments so that the clock does not wrap;
the adequacy theorem's receipt bound exceeds the execution's length, so the examples' closed
theorems are about executions of fewer than `2^63` steps (`counter/Adequacy.lean`, "The length
bound"), the highest the proof allows.
-/
module

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace lintest

/-- **`CounterClock`'s cap on the length of an execution**: `2^63` steps (see the file header). -/
abbrev counterClockStepBound : Nat := 2 ^ 63

end lintest
end EtcdGrove
end Perennial
