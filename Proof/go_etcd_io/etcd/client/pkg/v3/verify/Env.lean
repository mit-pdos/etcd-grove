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
  checks' specs require it. Read as `True`, every axiom about it holds (`Start.lean`'s
  satisfiability argument: `os.Getenv` is names-only, so a model whose `Getenv` returns `""`
  satisfies its spec's `envVerifyOff` clause).
* (etcdstorage, 2026-11-20) **Where it is used:** `os.Getenv`'s spec says that under it the value
  read for `ETCD_VERIFY` is `etcdVerifyOffValue` (lower-cased by Go's `strings.ToLower`, it is none
  of `all`, `assert`, `lock`): the axiom-level form of `verifyEnvOff`, on the one function that reads
  the environment (`notes/axiom-review/getenv-etcd-verify.md`). The checks (`verify.IsVerificationEnabled`,
  the backend's lock checks) are proved over it; until then each check was an axiom taking the token.
-/
module

public import Perennial.GooseLang.Lang
public import Perennial.ProgramLogic.Bounds
public import Proof.strings.Lower

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

/-- **A value of `ETCD_VERIFY` that enables no check** (etcdstorage, 2026-11-20): its lower-case form
(`strings.ToLower`, as `verify.getEnvVerify` takes it; `strings.lowersTo`) is none of `all`,
`assert`, `lock` (what `verifyEnvOff` says of the run's value). `os.Getenv`'s spec gives it of the
value it reads for `ETCD_VERIFY` under `envVerifyOff`. -/
def etcdVerifyOffValue (v : GoString) : Prop :=
  strings.lowersTo v go!"all" = false ∧ strings.lowersTo v go!"assert" = false ∧
    strings.lowersTo v go!"lock" = false

/-- The token of `verifyEnvOff` in the logic (axiomatized; see the file header). -/
axiom envVerifyOffTok {GF : BundledGFunctors} [GooseExts] : IProp GF

/-- **`ETCD_VERIFY` is off for the whole run** (persistent; see the file header). -/
def envVerifyOff {GF : BundledGFunctors} [GooseExts] : IProp GF := iprop(□ envVerifyOffTok)

instance envVerifyOff_persistent {GF : BundledGFunctors} [GooseExts] :
    Persistent (envVerifyOff (GF := GF)) := by
  unfold envVerifyOff; infer_instance

end EtcdGrove
end Perennial
