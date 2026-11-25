/-
`os.Getenv(key)` (names-only in Perennial): the value of the environment variable `key`, or
`""`; the spec says it returns some string (the environment is the deployment's), and (2026-11-25, the
owner's decision; from etcdstorage, 2026-11-20, under the token `envVerifyOff`) that for
`ETCD_VERIFY`, under the premise `EtcdVerifyOff`, the value it returns enables no check
(`etcdVerifyOffValue`; `Proof/go_etcd_io/etcd/client/pkg/v3/verify/Env.lean`). Go's `os.Getenv` reads the
process's environment (`syscall.Getenv`, the copy of `envs` taken at start, `syscall/env_unix.go`), which only
`os.Setenv`/`Unsetenv`/`Clearenv` change (`notes/axiom-review/getenv-etcd-verify.md`).

**Only offness, never the value** (2026-11-25, review: `notes/axiom-review/getenv-etcd-verify.md`). An
earlier draft returned `v = etcdVerifyEnv`, one opaque value for every read on every machine and boot; a
proof could then show two processes read equal values, which is false (process A unset, process B
`ETCD_VERIFY=0`: both off, but different; Go: a program checking equality panics). Read over every value
of the opaque `etcdVerifyEnv`, the premise `EtcdVerifyOff` with this post covers exactly the deployments in
which every process's value is off (instantiate the value at `""`, `etcdVerifyOffValue_unset`): no code of
a process sets the variable (`os.Setenv`, `Unsetenv`, `Clearenv` have no spec, so no verified code can),
so each read returns that process's own value. A process environment in `os`'s semantics is deferred
(with `GODEBUG`).

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
      ⌜key = go!"ETCD_VERIFY" → EtcdVerifyOff → etcdVerifyOffValue v⌝ }}

end spec

end EtcdGrove
end Perennial
