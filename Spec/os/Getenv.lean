/-
`os.Getenv(key)` (names-only in Perennial): the value of the environment variable `key`, or
`""`; the spec says it returns some string (the environment is the deployment's), and (etcdstorage,
2026-11-20) that the value of `ETCD_VERIFY` enables no check of etcd's (`etcdVerifyOffValue`) when the
run has it off (`envVerifyOff`, given at program start under `verifyEnvOff`): Go's `os.Getenv` reads
the process's environment (`syscall.Getenv`, the copy of `envs` taken at start, `syscall/env_unix.go`),
which only `os.Setenv`/`Unsetenv`/`Clearenv` change, and `verifyEnvOff` says the value is off at start
and no code of the run sets it (`notes/axiom-review/getenv-etcd-verify.md`). The trust boundary: an axiom, `Proof/os/Getenv.lean`. (2026-11-04) Stated for any `hlc`
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
      envVerifyOff -∗ ⌜key = go!"ETCD_VERIFY" → etcdVerifyOffValue v⌝ }}

end spec

end EtcdGrove
end Perennial
