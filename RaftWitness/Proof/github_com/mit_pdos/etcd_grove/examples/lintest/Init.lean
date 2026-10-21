/- Lean-first (no Rocq counterpart).

# lintest's package initialization (2026-10-19)

`wp_initialize'`: lintest's `initialize'` initializes porcupine (which initializes `context`,
`Proof/github_com/anishathalye/porcupine/Init.lean`), `time`, `sync/atomic` and `sync`, then
the package (no package-level variable). It returns `context`'s `isClosedchanInit` beside the
package's `isPkgInit`, at a table whose entry for lintest carries it too (as porcupine's,
`PorcupineInitTable`), so that a second initialization, from the map, gives it as well.
-/
-- The copy for the parallel tree `RaftWitness/` of `Proof/github_com/mit_pdos/etcd_grove/examples/lintest/Init.lean` (`PART_INITS` in
-- `etc/gen-init.py`): the same, but its imports of the copied modules and of raft are the part's.
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Base
public import RaftWitness.Proof.github_com.anishathalye.porcupine.Init
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import RaftWitness.Proof.runtime.PkgInitExt

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

/-! The ordinary form (decision D19e), for a package of the ordinary form importing this one, at
a table of its closure's `isPkgInit`s (see `CLOSEDCHAN` in `etc/gen-init.py`). -/
section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace github_com.mit_pdos.etcd_grove.examples.lintest

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.github_com.anishathalye.porcupine.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish

end github_com.mit_pdos.etcd_grove.examples.lintest

end init

end Perennial
