/-
Lean-first (no Rocq counterpart).

# The `durable` package: package initialization (2026-10-31)

`github.com/mit-pdos/etcd-grove/examples/durable` is the Go side of the GooseLang extension
`durableExt` (`GooseLang/Ext/Durable/`): its functions `Read` and `Write` are trusted, modeled by
the extension's operations (`TrustedCode/github_com/mit_pdos/etcd_grove/examples/durable.lean`),
and the rest of the package (its mutex `mu`, `tryWrite`) is translated names-only. Its
`initialize'` runs only `package.init` (no import, no translated variable: `mu` is untranslated
and the initializer does not run it), so its package fact is `True`.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.durable

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.durable

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.durable.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.durable :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.durable :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.durable

end Perennial
