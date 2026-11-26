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
start, `copyenv` once); the copy changes only through `syscall.Setenv`/`Unsetenv`/`Clearenv` (`os`'s wrappers, `golang.org/x/sys/unix`'s,
the runtime's `runtimeSetenv` family); every one of them is names-only with no spec here or in Perennial, so no
verified code calls them, and the Go dependency closure of the deployment's programs (`go list -deps` of
`examples/etcd/dist/{server,client}`, 2026-11-24 review) has no non-test caller (only etcd's and bbolt's `verify`
test helpers, which nothing there calls). A C `setenv` under cgo does not change Go's copy (measured). With a key
duplicated in the raw environment, the first occurrence is what `os.Getenv` and net/http both see. `osEnvIs` is
opaque and per process run: the predicate takes the `HeapGS` `⟨G, L⟩`, whose local part `L` the distributed
adequacy binds universally per machine and afresh at each restart (`nodeWp`), so a fact read on one machine, or
before a crash, cannot be used on another or after it.

Who relies on it: the axioms that take the absence of a proxy (`etcd_dist.noProxyEnv`, `NewServer_dist`): net/http
reads the proxy variables once, at the first call of `ProxyFromEnvironment` (the first request through a
`Transport` whose `Proxy` it is; `envProxyFunc`'s `sync.Once`, `httpproxy.FromEnvironment`'s `os.Getenv`), after the
program's own check read them.

Retired by an `os` model whose environment is the process's state (`notes/etcd-dist-plan.md` §15.2 (e): one value
per key per run, a persistent agreement), which would also retire `verifyEnvOff`/`envVerifyOffTok`. -/
axiom os.Getenv.wp_proofEnv : os.Getenv.specEnv (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
