/-
Specs of the trusted models of `os` (`Perennial/TrustedCode/os.lean`) that `os`'s initializer
runs: `runtime_args` (an arbitrary `[]string`), and the standard streams' initializers (`Stdin`,
`Stdout`: nothing; `Stderr`: the variable holds some pointer), as Perennial's `Proof/os/Models.lean`
(2026-11-07: this repository's `os`, project bboltfs's, carries the same models). `os`'s
initializer is `Init.lean` (generated, `etc/gen-init.py`).
-/
module

public import LinuxFs.Proof.syscall.Models
public import LinuxFs.Code.os

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace os

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The model of `runtime_args` returns some slice of strings, owned with its capacity. -/
theorem wp_runtime_args_impl :
    {{ (True : IProp GF) }}
      (App (Val runtime_args.impl) (Val #()))
    {{ (s : GoSlice), RET #s; ∃ xs : List GoString,
        s ↦* xs ∗ ownSliceCap GoString s (DFrac.own 1) }} :=
  syscall.wp_arbitraryStrings

/-- `Stdin`'s initializer (the model) does nothing. -/
theorem wp_Stdin_init :
    {{ (True : IProp GF) }} (App (Val Stdin.init) (Val #())) {{ RET #(); True }} := by
  wp_start
  iapply HΦ; itrivial

/-- `Stdout`'s initializer (the model) does nothing. -/
theorem wp_Stdout_init :
    {{ (True : IProp GF) }} (App (Val Stdout.init) (Val #())) {{ RET #(); True }} := by
  wp_start
  iapply HΦ; itrivial

/-- `Stderr`'s initializer (the model) allocates the variable and stores some pointer
(an arbitrary non-`nil` address, `GoPrealloc`). -/
theorem wp_Stderr_init :
    {{ (True : IProp GF) }} (App (Val Stderr.init) (Val #()))
    {{ RET #(); ∃ f : Loc, globalAddr Stderr ↦ f }} := by
  wp_start
  wp_apply wp_GlobalAlloc (V := Loc) go!"os.Stderr"
    (go.GoType.PointerType (go.GoType.Named go!"os.File" [])) as HS
  wp_apply wp_GoPrealloc as %l -
  iapply HΦ
  iexists _
  unfold Stderr
  iexact HS

end wps

end os

end Perennial
