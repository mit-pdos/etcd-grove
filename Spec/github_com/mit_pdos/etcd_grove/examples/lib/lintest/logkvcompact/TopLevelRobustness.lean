/- Lean-first (no Rocq counterpart).

# `lib/lintest/logkvcompact`: the top-level robustness result, stated

`logkvcompact_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvcompact/TopLevelRobustness.lean`.

- **The deployment**: one machine that never crashes (`stable`; no crashing machine, no fault),
  running `logkvcompactProgram` (`TopLevelDefs.lean`): the package's initialization, then `Main()`
  (`examples/lib/lintest/logkvcompact/logkvcompact.go`). `Main` runs between 1 and 8 clients (a
  random number) of between 1 and 32 operations each, each at random a write of one of eight values
  or a read, against logkv's log-applied register, its applied entries dropped from the log; traces
  them with `lintest.CounterClock()`; checks the trace with porcupine (no timeout); and panics
  unless porcupine answers `Ok`. So no panic means porcupine accepted every trace of every run.
- **Extensions**: none (`Robustness.noExts`, `Robustness/NoExts.lean`): GooseLang's semantics alone.
- **Premises**: only the package's `Assumptions` (each name's translated body or Perennial's model,
  recursively for the imports); no premise on the state or the environment.
- **Bounds**: `bound := counterClockStepBound` (`2^63`, `lintest/StepBound.lean`): the clock is an
  `atomic.Int64` incremented once per reading, which the proof keeps from wrapping by bounding the
  execution's length; the highest bound the proof allows. `threads := counterClockStepBound + 1`: no
  cap of its own (a run of fewer than `bound` steps has fewer than `bound + 1` threads).
- **Trusted**: GooseLang's semantics; Perennial's translations and models of the standard library
  the program calls (`sync`'s `Mutex`, `Cond`, `WaitGroup`, `sync/atomic`, `time`, `context`,
  `primitive.RandomUint64`). Porcupine (the vendored v1.3.1, `third_party/porcupine`) is translated
  and proved, not trusted. The axioms the theorem rests on are tracked in
  `etc/tcb-collections/lintest.txt`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvcompact.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace lintest

namespace logkvcompact

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] Robustness.noExts Robustness.noExtsSemantics Robustness.noExtsInterp

section adequacy

variable [go_gctx : GoGlobalContext]

/-- **`logkvcompact_adequate` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): `logkvcompactProgram` alone on one machine that never crashes, a fresh
Go process with no extension (`Robust`'s premise): in every execution of fewer than
`counterClockStepBound` (`2^63`) steps no thread is stuck and none has an unrecovered panic. -/
def logkvcompact_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvcompact.Assumptions]
    (σ : state) (g : GlobalState),
    Robustness.Robust [] [(logkvcompactProgram, σ)] g (threads := counterClockStepBound + 1)
      (bound := counterClockStepBound)

end adequacy
end logkvcompact
end lintest
end EtcdGrove
end Perennial

end
