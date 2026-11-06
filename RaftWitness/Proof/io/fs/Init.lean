/-
Package initialization of `io.fs`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
-- The copy for the parallel tree `RaftWitness/` of `Proof/io/fs/Init.lean` (`PART_INITS` in
-- `etc/gen-init.py`): the same, but its imports of the copied modules and of raft are the part's.
module

public import Proof.os.PkgInit
public import RaftWitness.Proof.runtime.PkgInitExt

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
namespace io.fs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `io.fs`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrInvalid.init,
        ErrPermission.init,
        ErrExist.init,
        ErrNotExist.init,
        ErrClosed.init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        SkipDir.init,
        SkipAll.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end io.fs
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.io.fs.Assumptions]

namespace io.fs

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.io.fs get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.io.fs }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk ErrInvalid.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrPermission.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNotExist.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrClosed.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk SkipDir.init (by mem_tac))
  wp_apply (opaqueInitsOk SkipAll.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.io.fs get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.io.fs }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end io.fs

end init

end Perennial
