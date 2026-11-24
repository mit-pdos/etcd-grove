/-
The trust boundary of `os.Getenv`'s second spec (`Spec/os/GetenvEnv.lean`).
-/
module

public import Spec.os.GetenvEnv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`os.Getenv(key)` returns the process's value of `key`, fixed for the run** (interim trust boundary,
2026-11-24; `notes/etcd-dist-plan.md` "Interim transport"). What it asserts: the value `v` returned is the
process's environment's for `key` (`""` when unset), and stays so for the rest of the run (`osEnvIs key v`).

Why it is true: Go's `os.Getenv` is `syscall.Getenv` (after `testlog.Getenv`, a no-op outside tests), which reads
the process's copy of the environment under `envLock` (`syscall/env_unix.go`: `envs`, copied from the process's
start, `copyenv` once); the copy changes only through `syscall.Setenv`/`Unsetenv`/`Clearenv` (and `os`'s wrappers),
which have no spec in this repository, so no verified code changes it, and the deployment's programs (all verified)
call none of them. `osEnvIs` is opaque and per process (`Proof/os/EnvIs.lean`), so a fact read on one machine
cannot be used on another, whose environment may differ.

Who relies on it: the axioms that take the absence of a proxy (`etcd_dist.noProxyEnv`, `NewServer_dist`): net/http
reads the proxy variables once, at its first proxied request (`envProxyFunc`'s `sync.Once`, through
`httpproxy.FromEnvironment`'s `os.Getenv`), after the program's own check read them.

Retired by an `os` model whose environment is the process's state (`notes/etcd-dist-plan.md` §15.2 (e): one value
per key per run, a persistent agreement), which would also retire `verifyEnvOff`/`envVerifyOffTok`. -/
axiom os.Getenv.wp_proofEnv : os.Getenv.specEnv (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
