/-
`os.Getenv(key)`, its second spec (2026-11-24, `notes/etcd-dist-plan.md` "Interim transport"): the value read is
the process's environment's for `key` for the whole run (`osEnvIs key v`, `Proof/os/EnvIs.lean`). The trust
boundary: an axiom, `Proof/os/GetenvEnv.lean`. Beside `os.Getenv.spec` (`Spec/os/Getenv.lean`, the
`ETCD_VERIFY` clause), not in place of it: both are true of Go's `os.Getenv`, and a proof uses one or the other.
Lean-first (no Rocq counterpart).
-/
module

public import Code.os
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Proof.os.EnvIs

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
abbrev os.Getenv.specEnv : Prop :=
  ∀ (key : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! os.Getenv)) (Val #key))
  {{ (v : GoString), RET #v; osEnvIs key v }}

end spec

end EtcdGrove
end Perennial
