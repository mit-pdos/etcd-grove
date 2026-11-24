/-
`syscall.Exit(code)` (this repository's `syscall`, project `bboltfs`; zap-z2, 2026-11-23, as Perennial's
`Spec/syscall/Exit.lean`): the trusted model `AngelicExit` (`TrustedCode/syscall.lean`) never returns.
Proved in `Proof/syscall/Exit.lean`. Lean-first.
-/
module

public import Code.syscall
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

/-- `Exit(code)` does not return: the process ends (`TrustedCode/syscall.lean`). -/
abbrev syscall.Exit.spec : Prop :=
  ∀ (code : w64),
  {{ (True : IProp GF) }}
    (App (Val (@! syscall.Exit)) (Val #code))
  {{ RET #(); False }}

end spec

end EtcdGrove
end Perennial
