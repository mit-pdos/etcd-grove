/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/assert.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
Cross-package spec of `pkg/assert`: `Assert(cond, format, args...)` returns when `cond` is true
(its callers establish `cond`; the panicking branch is never reached, so no `fmt` spec is
needed).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.assert.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : assert.Assumptions]

set_option goose.wp.extras true

/-- `Assert(true, format, args)` returns. -/
abbrev assert.Assert.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.assert }}
    (App (App (App (Val (@! assert.Assert)) (Val #true)) (Val #format)) (Val #args))
  {{ RET #(); True }}

end spec

end Perennial.github_com.tangledbytes.go_vsr.pkg
