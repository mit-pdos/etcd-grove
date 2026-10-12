/- Lean-first (no Rocq counterpart).

# The register package's initialization (2026-10-12)

`register.wp_initialize'`: running the package's `initialize'` from `ownInitializing`
initializes its imports (`context`, `time`, raft, `raftpb`, `encoding/binary`, `sync`) and
then the package (no package-level variable), and gives its `isPkgInit`. It takes raft's
premises (`Proof/go_etcd_io/raft/v3/Init.lean`): the method-set fact
`context.ErrorStringIsError` and the model of `log.New`, `log.NewModel`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Base
public import Proof.go_etcd_io.raft.v3.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.register

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [context.ErrorStringIsError] [log.NewModel]

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.register
      get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
  wp_apply encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
  wp_apply go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply go_etcd_io.raft.v3.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply time.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply context.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
  iframe Hown
  is_pkg_init_finish

end init

end github_com.mit_pdos.etcd_grove.examples.register

end Perennial
