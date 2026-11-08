/-
**`ETCD_VERIFY` is off** (sweep repairs 1, B4, 2026-11-07; the user's narrowing (b) via
etcd-grove-82). Lean-first.

etcd's `verify` package reads the environment variable `ETCD_VERIFY` at every call
(`verify.IsVerificationEnabled`, `client/pkg/verify/verify.go`): with it set to `all`, `assert` or
`lock` (case-insensitive), the backend's lock checks (`ValidateCalledInsideApply`,
`ValidateCalledOutSideApply`, `ValidateCalledInsideUnittest`) and `VerifyBackendConsistency` run
their checks, which panic outside the apply loop or on an inconsistent backend. Production leaves
it unset; only etcd's test helpers (`client/pkg/testutil/before.go`,
`tests/framework/integration/testing.go`) set it.

* `verifyEnvOff e` (a proposition, a hypothesis of each closed theorem that starts a server): in a
  run of `e` the variable is off from the start, and no code of `e` sets it.
* `envVerifyOff` (persistent): its token in the logic. Program start gives it
  (`goose_adequacy_start`, under `verifyEnvOff e`; `startRights`); nothing else produces it. The
  four checks' specs require it. Read as `True`, every axiom about it holds (`Start.lean`'s
  satisfiability argument).
-/
module

public import Perennial.GooseLang.Lang
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- **`ETCD_VERIFY` disables etcd's runtime checks for the whole run of `e`** (a fact of the
environment a run of `e` is in, and of `e`'s unverified code): when `e` starts, the variable is
unset, or its lower-cased value is none of `all`, `assert`, `lock`; and no code of `e` sets it
(`os.Setenv`/`os.Unsetenv` have no spec here, so no verified code can). Go evidence:
`examples/sweeprepairs/b1` (`TestB4Startup`, `TestB4Off`, `TestB4On`). -/
axiom verifyEnvOff [GooseExts] (e : Expr) : Prop

/-- The token of `verifyEnvOff` in the logic (axiomatized; see the file header). -/
axiom envVerifyOffTok {GF : BundledGFunctors} [GooseExts] : IProp GF

/-- **`ETCD_VERIFY` is off for the whole run** (persistent; see the file header). -/
def envVerifyOff {GF : BundledGFunctors} [GooseExts] : IProp GF := iprop(□ envVerifyOffTok)

instance envVerifyOff_persistent {GF : BundledGFunctors} [GooseExts] :
    Persistent (envVerifyOff (GF := GF)) := by
  unfold envVerifyOff; infer_instance

end EtcdGrove
end Perennial
