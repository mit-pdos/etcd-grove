/-
**`ETCD_VERIFY` is off** (sweep repairs 1, B4, 2026-11-07; the user's narrowing (b) via
etcd-grove-82; restated over a concrete reading of the environment, the owner's decision of
2026-11-25). Lean-first.

etcd's `verify` package reads the environment variable `ETCD_VERIFY` at every call
(`verify.IsVerificationEnabled`, `client/pkg/verify/verify.go`): with it set to `all`, `assert` or
`lock` (case-insensitive), the backend's lock checks (`ValidateCalledInsideApply`,
`ValidateCalledOutSideApply`, `ValidateCalledInsideUnittest`) and `VerifyBackendConsistency` run
their checks, which panic outside the apply loop or on an inconsistent backend. Production leaves
it unset; only etcd's test helpers (`client/pkg/testutil/before.go`,
`tests/framework/integration/testing.go`) set it.

An environment premise, as Perennial's `crypto.fips140.GodebugFips140Off`
(`TrustedCode/crypto/fips140.lean`: an opaque `godebugFips140` and a definition over it):

* `etcdVerifyEnv` (opaque): the value `os.Getenv("ETCD_VERIFY")` returns in the run (`""` when
  unset). `os.Getenv`'s spec (`Spec/os/Getenv.lean`, an axiom) returns exactly it for that key.
* `EtcdVerifyOff` (a definition): that value enables no check (`etcdVerifyOffValue`). A plain
  premise `(HEnv : EtcdVerifyOff)` of each closed theorem that starts a server; the checks
  (`verify.IsVerificationEnabled`, the backend's lock checks, `VerifyBackendConsistency`) are proved
  under it, and the specs that need it carry it as `⌜EtcdVerifyOff⌝`.
* `etcdVerifyOffValue_unset`: the premise is satisfiable: the value of an unset variable, `""`,
  enables no check.

Until 2026-11-25: an axiomatized proposition of the program, `verifyEnvOff e`, and its token in the
logic, the axiomatized `envVerifyOffTok` (`envVerifyOff := □ envVerifyOffTok`), handed out by program
start (`goose_adequacy_start`) under `verifyEnvOff e`; no witness could satisfy an axiom constant
(`notes/decisions.md`, "`ETCD_VERIFY` as an environment premise over its value").
-/
module

public import Perennial.GooseLang.Lang
public import Perennial.ProgramLogic.Bounds
public import Proof.strings.Lower

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **The value of `ETCD_VERIFY` in the run** (`""` when the variable is unset): what
`os.Getenv("ETCD_VERIFY")` returns (`os.Getenv`'s spec). The model has no process environment, so
the value is a constant: one value for every read of a run, and for every machine of a deployment,
as Perennial's `godebugFips140` for `GODEBUG`. Faithful as long as no code of the run sets the
variable: Go's `os.Getenv` reads the process's copy of its initial environment, which only
`os.Setenv`/`Unsetenv`/`Clearenv` change, and none of them has a spec here, so no verified code
calls them (`notes/axiom-review/getenv-etcd-verify.md`). A process environment in `os`'s semantics
(per process, with `Setenv`) is deferred. -/
opaque etcdVerifyEnv : GoString

/-- **A value of `ETCD_VERIFY` that enables no check** (etcdstorage, 2026-11-20): its lower-case form
(`strings.ToLower`, as `verify.getEnvVerify` takes it; `strings.lowersTo`) is none of `all`,
`assert`, `lock`. -/
def etcdVerifyOffValue (v : GoString) : Prop :=
  strings.lowersTo v go!"all" = false ∧ strings.lowersTo v go!"assert" = false ∧
    strings.lowersTo v go!"lock" = false

/-- **`ETCD_VERIFY` disables etcd's runtime checks for the run** (an environment premise of each
closed theorem that starts a server, as `crypto.fips140.GodebugFips140Off`): the run's value of the
variable (`etcdVerifyEnv`, `""` when unset) enables no check. Go evidence:
`examples/sweeprepairs/b1` (`TestB4Startup`, `TestB4Off`, `TestB4On`). -/
def EtcdVerifyOff : Prop := etcdVerifyOffValue etcdVerifyEnv

/-- **The premise is satisfiable**: the variable unset (`os.Getenv` returns `""`) enables no
check. -/
theorem etcdVerifyOffValue_unset : etcdVerifyOffValue go!"" := by
  unfold etcdVerifyOffValue; decide

end EtcdGrove
end Perennial
