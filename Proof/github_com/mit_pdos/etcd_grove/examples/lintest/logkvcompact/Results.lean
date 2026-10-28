/-
Lean-first (no Rocq counterpart).

# lintest/logkvcompact: the results (2026-10-28)

- **`logkvcompact.wp_Main`** (`Link.lean`): `Main()` returns (never panics), so porcupine answered `Ok`
  on the trace of 4 clients of 10 operations of the log-applied register, for executions of
  fewer than `2^63` steps (`receiptBound GF ≤ 2^63`, `CounterClock`'s premise), given
  `context`'s `isClosedchanInit`; every callee linked (the register's proofs, the driver's and
  porcupine's), under `[NaInvG GF]` (porcupine's camera of non-atomic invariants, which
  Perennial's `allG` does not provide: `notes/STATUS.md`, "Porcupine").
- **`logkvcompact_adequate`** (`Adequacy.lean`): the same as a closed theorem about the operational
  semantics of `initialize'(); Main()` from a fresh state, with no Iris in its statement and no
  instance assumed (the bundle `logkvcompactGF` provides `NaInvG`). The end-to-end result.

`#print axioms` of each is its trust base.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Adequacy

@[expose] public section

#print axioms Perennial.EtcdGrove.lintest.logkvcompact.wp_Main
#print axioms Perennial.EtcdGrove.lintest.logkvcompact.logkvcompact_adequate
