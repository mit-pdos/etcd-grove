/- Lean-first (no Rocq counterpart).

# lintest's package initialization (2026-10-19)

`wp_initialize'`: lintest's `initialize'` initializes porcupine (which initializes `context`,
`Proof/github_com/anishathalye/porcupine/Init.lean`), `time`, `sync/atomic` and `sync`, then
the package (no package-level variable). It returns `context`'s `isClosedchanInit` beside the
package's `isPkgInit`, at a table whose entry for lintest carries it too (as porcupine's,
`PorcupineInitTable`), so that a second initialization, from the map, gives it as well.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Base
public import Proof.github_com.anishathalye.porcupine.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lintest

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

/-- lintest's initialization, returning `context`'s `isClosedchanInit` (see the file header). -/
theorem wp_initialize' [context.ErrorStringIsError] [context.DeadlineExceededIsError]
    (get_is_pkg_init : GoString → IProp GF)
    (Ht : github_com.anishathalye.porcupine.PorcupineInitTable get_is_pkg_init)
    (Hself : get_is_pkg_init pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest =
      iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest ∗
        context.isClosedchanInit)) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        (isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest ∗
          context.isClosedchanInit) }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hself) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply github_com.anishathalye.porcupine.wp_initialize' _ Ht $$ Hown as ⟨Hown, #H4, #Hcc⟩
  wp_apply time.wp_initialize' _ Ht.time $$ Hown as ⟨Hown, #H3⟩
  wp_apply sync.atomic.wp_initialize' _ Ht.atomic $$ Hown as ⟨Hown, #H2⟩
  wp_apply sync.wp_initialize' _ Ht.sync $$ Hown as ⟨Hown, #H1⟩
  iframe Hown
  imodintro
  iframe #
  is_pkg_init_finish

end init

end github_com.mit_pdos.etcd_grove.examples.lintest

end Perennial
