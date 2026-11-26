/-
**What the process's environment holds** (2026-11-24, `notes/etcd-dist-plan.md` "Interim transport"). Lean-first.

`osEnvIs key v` (persistent, of one process: it takes the process's `HeapGS`): a call `os.Getenv(key)` of this
process returned `v`. It is produced only by `os.Getenv`'s second spec (`os.Getenv.specEnv`,
`Spec/os/GetenvEnv.lean`, an axiom) and has no law. Its meaning, which the axioms that take it rely on: **the
process's environment maps `key` to `v` (`v = ""`: unset or empty) for the whole run.** Go's `os.Getenv` reads the
process's copy of the environment (`syscall.Getenv` over `envs`, taken at start, `syscall/env_unix.go`), which
only `os.Setenv`/`os.Unsetenv`/`os.Clearenv` (and `syscall`'s, `golang.org/x/sys/unix`'s) change; none of them
has a spec here, so no verified code calls them (and no non-test code of the deployment's Go closure does), and every later read of `key` in the process (net/http's proxy configuration included) sees `v`.

It is per process run: an `osEnvIs` of one machine says nothing of another's environment, nor of the same machine's
after a restart (the opaque `osEnvRaw` takes the `HeapGS` `⟨G, L⟩`, whose `L` the distributed adequacy binds
universally per machine and per boot). Read as `True`, the axiom producing it holds.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The trusted text of `osEnvIs` (opaque, no law; see the file header). Its body is never unfolded; it takes the process's `HeapGS` explicitly. -/
opaque osEnvRaw (h : HeapGS hlc GF) (key v : GoString) : IProp GF := iprop(True)

/-- **This process's environment maps `key` to `v`** (persistent; see the file header). -/
def osEnvIs (key v : GoString) : IProp GF := iprop(□ osEnvRaw hG key v)

instance osEnvIs_persistent (key v : GoString) : Persistent (osEnvIs (hG := hG) key v) := by
  unfold osEnvIs; infer_instance

end defs

end EtcdGrove
end Perennial
