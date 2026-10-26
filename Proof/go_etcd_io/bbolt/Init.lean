/-
Package initialization of `go_etcd_io.bbolt`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.bbolt.internal.common.Initialize
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.bbolt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.bbolt`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([trySolo.init,
        DefaultOptions.init,
        ErrDatabaseNotOpen.init,
        ErrInvalid.init,
        ErrInvalidMapping.init,
        ErrVersionMismatch.init,
        ErrChecksum.init,
        ErrTimeout.init,
        ErrTxNotWritable.init,
        ErrTxClosed.init,
        ErrDatabaseReadOnly.init,
        ErrFreePagesNotLoaded.init,
        ErrBucketNotFound.init,
        ErrBucketExists.init,
        ErrBucketNameRequired.init,
        ErrKeyRequired.init,
        ErrKeyTooLarge.init,
        ErrValueTooLarge.init,
        ErrIncompatibleValue.init,
        discardLogger.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end go_etcd_io.bbolt
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.bbolt.Assumptions]

namespace go_etcd_io.bbolt

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.bbolt get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.go_etcd_io.bbolt.internal.common.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk trySolo.init (by mem_tac))
  wp_apply (opaqueInitsOk DefaultOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrDatabaseNotOpen.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInvalid.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInvalidMapping.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrVersionMismatch.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrChecksum.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTxNotWritable.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTxClosed.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrDatabaseReadOnly.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrFreePagesNotLoaded.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrBucketNotFound.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrBucketExists.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrBucketNameRequired.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrKeyRequired.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrKeyTooLarge.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrValueTooLarge.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrIncompatibleValue.init (by mem_tac))
  wp_apply (opaqueInitsOk discardLogger.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.bbolt get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.bbolt

end init

end Perennial
