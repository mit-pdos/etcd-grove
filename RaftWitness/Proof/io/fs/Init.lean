/-
Package initialization of `io.fs`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`Proof/os/PkgInit.lean`): its five error variables, which `os`'s initializer
copies, hold some error for good. Its initializer copies internal/oserror's errors into them
(`errInvalid()`, ...) and makes `SkipDir` and `SkipAll` (`errors.New`).
-/
-- The copy for the parallel tree `RaftWitness/` of `Proof/io/fs/Init.lean` (`PART_INITS` in
-- `etc/gen-init.py`): the same, but its imports of the copied modules and of raft are the part's.
module

public import Proof.os.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.internal.oserror.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.internal.oserror.Link
public import Perennial.Proof.errors.NewVar
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
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _) SkipAll _ as HSkipAll
  wp_apply wp_GlobalAlloc (V := _) SkipDir _ as HSkipDir
  wp_apply wp_GlobalAlloc (V := _) ErrClosed _ as HErrClosed
  wp_apply wp_GlobalAlloc (V := _) ErrNotExist _ as HErrNotExist
  wp_apply wp_GlobalAlloc (V := _) ErrExist _ as HErrExist
  wp_apply wp_GlobalAlloc (V := _) ErrPermission _ as HErrPermission
  wp_apply wp_GlobalAlloc (V := _) ErrInvalid _ as HErrInvalid
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.internal.oserror _root_.Perennial.internal.oserror.initialize'
      EtcdGrove.ExternalInit.internal_oserror _root_.Perennial.internal.oserror.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrInvalid))
  -- translated initializer of ErrPermission))
  -- translated initializer of ErrExist))
  -- translated initializer of ErrNotExist))
  -- translated initializer of ErrClosed))
  -- translated initializer of SkipDir))
  -- translated initializer of SkipAll))
  ihave #Hos := _root_.Perennial.internal.oserror.isInit_access $$ Hd2
  icases Hos with ⟨#VIn, #VPe, #VEx, #VNE, #VCl⟩
  iunfold _root_.Perennial.errors.newVar at VIn VPe VEx VNE VCl
  icases VIn with ⟨%xIn, #OIn, #EIn⟩
  icases VPe with ⟨%xPe, #OPe, #EPe⟩
  icases VEx with ⟨%xEx, #OEx, #EEx⟩
  icases VNE with ⟨%xNE, #ONE, #ENE⟩
  icases VCl with ⟨%xCl, #OCl, #ECl⟩
  wp_func_call
  wp_call
  wp_auto
  ipersist HErrInvalid
  wp_func_call
  wp_call
  wp_auto
  ipersist HErrPermission
  wp_func_call
  wp_call
  wp_auto
  ipersist HErrExist
  wp_func_call
  wp_call
  wp_auto
  ipersist HErrNotExist
  wp_func_call
  wp_call
  wp_auto
  ipersist HErrClosed
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xSD #ESD
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xSA #ESA
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
