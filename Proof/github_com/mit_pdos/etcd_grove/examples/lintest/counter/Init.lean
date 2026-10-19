/- Lean-first (no Rocq counterpart).

# The counter package's initialization (2026-10-19)

`wp_initialize'`: the counter's `initialize'` initializes lintest (which initializes porcupine,
which initializes `context`: `Proof/github_com/anishathalye/porcupine/Init.lean`), porcupine,
`time` and `sync`, then the package (no package-level variable). It returns `context`'s
`isClosedchanInit`, which `Main.spec` takes, beside the package's `isPkgInit`, at a table whose
entries for `context`, porcupine, lintest and the counter carry it (`PorcupineInitTable` and
the two equations).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lintest.counter

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

/-- The counter's initialization, returning `context`'s `isClosedchanInit` (see the file
header). -/
theorem wp_initialize' [context.ErrorStringIsError] [context.DeadlineExceededIsError]
    (get_is_pkg_init : GoString → IProp GF)
    (Ht : github_com.anishathalye.porcupine.PorcupineInitTable get_is_pkg_init)
    (Hlintest : get_is_pkg_init pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest =
      iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest ∗
        context.isClosedchanInit))
    (Hself : get_is_pkg_init pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter =
      iprop(isPkgInit (PROP := IProp GF)
          pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter ∗
        context.isClosedchanInit)) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        (isPkgInit (PROP := IProp GF)
            pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter ∗
          context.isClosedchanInit) }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hself) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply github_com.mit_pdos.etcd_grove.examples.lintest.wp_initialize' _ Ht Hlintest
    $$ Hown as ⟨Hown, #H4, #Hcc⟩
  wp_apply github_com.anishathalye.porcupine.wp_initialize' _ Ht $$ Hown as ⟨Hown, #H3, -⟩
  wp_apply time.wp_initialize' _ Ht.time $$ Hown as ⟨Hown, #H2⟩
  wp_apply sync.wp_initialize' _ Ht.sync $$ Hown as ⟨Hown, #H1⟩
  iframe Hown
  imodintro
  iframe #
  is_pkg_init_finish

end init

end github_com.mit_pdos.etcd_grove.examples.lintest.counter

end Perennial
