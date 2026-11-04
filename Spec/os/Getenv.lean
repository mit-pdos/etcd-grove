/-
`os.Getenv(key)` (names-only in Perennial): the value of the environment variable `key`, or
`""`; the spec says it returns some string (the environment is the deployment's). The trust boundary: an axiom, `Proof/os/Getenv.lean`. (2026-11-04) Stated for any `hlc`
(it was for `HasLC.hasLC` only), so that bbolt's specs, which are, can call it (`internal/common`'s
`getEnvVerify`). Lean-first (no Rocq counterpart).
-/
module

public import Code.os
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

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
  {{ (v : GoString), RET #v; True }}

end spec

end EtcdGrove
end Perennial
