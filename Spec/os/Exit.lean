/-
`os.Exit(code)` (this repository's `os`, project `bboltfs`; zap-z2, 2026-11-23, as Perennial's
`Spec/os/Exit.lean`): translated (`if code == 0 && testlog.PanicOnExit0() { panic(...) }`,
`runtime_beforeExit(code)`, `syscall.Exit(code)`), over the trusted `runtime_beforeExit` (nothing) and
`syscall.Exit` (`AngelicExit`). Proved in `Proof/os/Exit.lean`. Lean-first.
-/
module

public import Code.os
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Perennial.Proof.internal.testlog.Base

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

/-- `Exit(code)` does not return (`syscall.Exit`); `Exit(0)` does not panic, since
`internal/testlog`'s flag is false (its `isPkgInit`: a program's start, not a test binary's). -/
abbrev os.Exit.spec : Prop :=
  ∀ (code : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.testlog }}
    (App (Val (@! os.Exit)) (Val #code))
  {{ RET #(); False }}

end spec

end EtcdGrove
end Perennial
