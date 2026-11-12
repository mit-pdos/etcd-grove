/-
Package initialization of `internal.poll`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`PkgInit.lean`): `ErrNoDeadline` and `ErrDeadlineExceeded`, which `os`'s
initializer copies, hold some error for good. Its initializer runs its variables' translated
initializers (`sync.OnceValue(...)`, `errors.New` errors, function values, a `sync.Pool`
literal).
-/
module

public import LinuxFs.Proof.internal.poll.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.sync.Link
public import LinuxFs.Proof.internal.syscall.unix.Init
public import LinuxFs.Proof.syscall.Init
public import Perennial.Proof.sync.Link
public import Perennial.Proof.errors.NewVar
public import LinuxFs.Proof.runtime.PkgInitExt

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
variable [package_sem : _root_.Perennial.internal.poll.Assumptions]

namespace internal.poll

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.internal.poll get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.internal.poll }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _) splicePipePool _ as HsplicePipePool
  wp_apply wp_GlobalAlloc (V := _) TestHookDidSendFile _ as HTestHookDidSendFile
  wp_apply wp_GlobalAlloc (V := _) AcceptFunc _ as HAcceptFunc
  wp_apply wp_GlobalAlloc (V := _) CloseFunc _ as HCloseFunc
  wp_apply wp_GlobalAlloc (V := _) Accept4Func _ as HAccept4Func
  wp_apply wp_GlobalAlloc (V := _) TestHookDidWritev _ as HTestHookDidWritev
  wp_apply wp_GlobalAlloc (V := _) ErrNotPollable _ as HErrNotPollable
  wp_apply wp_GlobalAlloc (V := _) ErrDeadlineExceeded _ as HErrDeadlineExceeded
  wp_apply wp_GlobalAlloc (V := _) ErrNoDeadline _ as HErrNoDeadline
  wp_apply wp_GlobalAlloc (V := _) ErrFileClosing _ as HErrFileClosing
  wp_apply wp_GlobalAlloc (V := _) ErrNetClosing _ as HErrNetClosing
  wp_apply wp_GlobalAlloc (V := _) errENOENT _ as HerrENOENT
  wp_apply wp_GlobalAlloc (V := _) errEINVAL _ as HerrEINVAL
  wp_apply wp_GlobalAlloc (V := _) errEAGAIN _ as HerrEAGAIN
  wp_apply wp_GlobalAlloc (V := _) supportCopyFileRange _ as HsupportCopyFileRange
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.syscall.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.internal.syscall.unix.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of supportCopyFileRange))
  -- translated initializer of errEAGAIN))
  -- translated initializer of errEINVAL))
  -- translated initializer of errENOENT))
  -- translated initializer of ErrNetClosing))
  -- translated initializer of ErrFileClosing))
  -- translated initializer of ErrNoDeadline))
  -- translated initializer of ErrDeadlineExceeded))
  -- translated initializer of ErrNotPollable))
  -- translated initializer of TestHookDidWritev))
  -- translated initializer of Accept4Func))
  -- translated initializer of CloseFunc))
  -- translated initializer of AcceptFunc))
  -- translated initializer of TestHookDidSendFile))
  -- translated initializer of splicePipePool))
  set_option maxRecDepth 20000 in
  wp_apply _root_.Perennial.sync.wp_OnceValue as %cfr -
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xFC #EFC
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xND #END
  ipersist HErrNoDeadline
  wp_alloc_anon
  wp_auto
  ipersist HErrDeadlineExceeded
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xNP #ENP
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.internal.poll get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.internal.poll }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end internal.poll

end init

end Perennial
