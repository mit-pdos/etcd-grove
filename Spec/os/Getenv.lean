/-
`os.Getenv(key)` (names-only in Perennial): the value of the environment variable `key`, or
`""`; the spec says it returns some string (the environment is the deployment's), and (2026-11-25, the
owner's decision; from etcdstorage, 2026-11-20, under the token `envVerifyOff`) that for
`ETCD_VERIFY` it returns exactly the run's value `etcdVerifyEnv`
(`Proof/go_etcd_io/etcd/client/pkg/v3/verify/Env.lean`). Go's `os.Getenv` reads the process's
environment (`syscall.Getenv`, the copy of `envs` taken at start, `syscall/env_unix.go`), which only
`os.Setenv`/`Unsetenv`/`Clearenv` change (`notes/axiom-review/getenv-etcd-verify.md`).

**What makes the post sound.** It names one value for every call, in every run of the model and on
every machine, so it holds only if every read of `ETCD_VERIFY` in a run returns the same value: no
code of the run sets the variable. No verified code can (`os.Setenv`, `Unsetenv` and `Clearenv` have
no spec here, so a proof cannot call them); unverified code of a deployment that did would falsify
it. The value is per run: `etcdVerifyEnv` is the value of the run the theorem is about (a theorem
over its value, `EtcdVerifyOff`, quantifies over no other run's environment), and is the same on
every machine of a deployment, as `GODEBUG`'s `godebugFips140` (a process environment in `os`'s
semantics is deferred). Stronger than the previous post (which said only, given `envVerifyOff`, that
the value enabled no check) in naming the value, and weaker in needing no token.

The trust boundary: an axiom, `Proof/os/Getenv.lean`. (2026-11-04) Stated for any `hlc`
(it was for `HasLC.hasLC` only), so that bbolt's specs, which are, can call it (`internal/common`'s
`getEnvVerify`). Lean-first (no Rocq counterpart).
-/
module

public import Code.os
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev os.Getenv.spec : Prop :=
  ∀ (key : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! os.Getenv)) (Val #key))
  {{ (v : GoString), RET #v;
      ⌜key = go!"ETCD_VERIFY" → v = etcdVerifyEnv⌝ }}

end spec

end EtcdGrove
end Perennial
