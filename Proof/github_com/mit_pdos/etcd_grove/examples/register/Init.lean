/- Lean-first (no Rocq counterpart).

# The register package's initialization (2026-10-12)

`register.wp_initialize'`: running the package's `initialize'` from `ownInitializing`
initializes its imports (`context`, `time`, raft, `raftpb`, `encoding/binary`, `sync`) and
then the package (no package-level variable), and gives its `isPkgInit`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.register

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.register
      get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register }} := by
  sorry

end init

end github_com.mit_pdos.etcd_grove.examples.register

end Perennial
