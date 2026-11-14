/-
Package initialization of `os`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`Proof/os/PkgInit.lean`): `Stderr` holds a fixed `*File`, which raft's
initializer loads (`defaultLogger`), `ErrExist` a non-nil error, `ErrNotExist` and
`ErrInvalid` some error, `ErrClosed` one `fmt` formats (io/fs's; the part only). `os` is this repository's translation (project bboltfs's): its
initializer initializes its imports and runs its variables' translated initializers (`errors.New`
errors, io/fs's and internal/poll's error variables, `sync.OnceValue`, function values) and the
trusted models of the standard streams' (`TrustedCode/os.lean`: `Stdin`, `Stdout` nothing, `Stderr`
an arbitrary in-range address with no cell, not reserved, `GoPrealloc`), then its translated `init`
function, which calls the trusted model of
`runtime_args` (an arbitrary `[]string`). (Until 2026-11-07 the trust-boundary axioms
`opaqueInitsOk`, `Stderr_init`, `initFuncsOk`; until 2026-11-03, over Perennial's `os`, in raft's
`Init.lean`.)
-/
module

public import LinuxFs.Proof.os.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sync.Link
public import LinuxFs.Proof.internal.poll.Init
public import LinuxFs.Proof.io.fs.Init
public import LinuxFs.Proof.syscall.Init
public import LinuxFs.Proof.os.Models
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
variable [package_sem : _root_.Perennial.os.Assumptions]

namespace os

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.os get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.os }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _) pollSplice _ as HpollSplice
  wp_apply wp_GlobalAlloc (V := _) pollCopyFileRange _ as HpollCopyFileRange
  wp_apply wp_GlobalAlloc (V := _) errPatternHasSeparator _ as HerrPatternHasSeparator
  wp_apply wp_GlobalAlloc (V := _) Args _ as HArgs
  wp_apply wp_GlobalAlloc (V := _) checkPidfdOnce _ as HcheckPidfdOnce
  wp_apply wp_GlobalAlloc (V := _) checkWrapErr _ as HcheckWrapErr
  wp_apply wp_GlobalAlloc (V := _) errPathEscapes _ as HerrPathEscapes
  wp_apply wp_GlobalAlloc (V := _) errWriteAtInAppendMode _ as HerrWriteAtInAppendMode
  wp_apply wp_GlobalAlloc (V := _) Kill _ as HKill
  wp_apply wp_GlobalAlloc (V := _) Interrupt _ as HInterrupt
  wp_apply wp_GlobalAlloc (V := _) ErrNoHandle _ as HErrNoHandle
  wp_apply wp_GlobalAlloc (V := _) errProcessReleased _ as HerrProcessReleased
  wp_apply wp_GlobalAlloc (V := _) ErrProcessDone _ as HErrProcessDone
  wp_apply wp_GlobalAlloc (V := _) ErrDeadlineExceeded _ as HErrDeadlineExceeded
  wp_apply wp_GlobalAlloc (V := _) ErrNoDeadline _ as HErrNoDeadline
  wp_apply wp_GlobalAlloc (V := _) ErrClosed _ as HErrClosed
  wp_apply wp_GlobalAlloc (V := _) ErrNotExist _ as HErrNotExist
  wp_apply wp_GlobalAlloc (V := _) ErrExist _ as HErrExist
  wp_apply wp_GlobalAlloc (V := _) ErrPermission _ as HErrPermission
  wp_apply wp_GlobalAlloc (V := _) ErrInvalid _ as HErrInvalid
  wp_apply wp_GlobalAlloc (V := _) dirBufPool _ as HdirBufPool
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.internal.poll.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.syscall.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.io.fs.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of dirBufPool))
  ihave #FS : (iprop((∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrInvalid) e DFrac.discard) ∗ (∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrPermission) e DFrac.discard) ∗ (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr _root_.Perennial.io.fs.ErrExist) e DFrac.discard) ∗ (∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.io.fs.ErrNotExist) e DFrac.discard) ∗ (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗ typedPointsto (globalAddr _root_.Perennial.io.fs.ErrClosed) e DFrac.discard)) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd2
  icases FS with ⟨⟨%fe1, #F1⟩, ⟨%fe2, #F2⟩, ⟨%fe3, %hfe3, #F3⟩, ⟨%fe4, #F4⟩, ⟨%fe5, #F5ok, #F5⟩⟩
  ihave #PL : (iprop((∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.internal.poll.ErrNoDeadline) e DFrac.discard) ∗ (∃ e : GoInterface, typedPointsto (globalAddr _root_.Perennial.internal.poll.ErrDeadlineExceeded) e DFrac.discard)) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd5
  icases PL with ⟨⟨%pe1, #P1⟩, ⟨%pe2, #P2⟩⟩
  repeat (first
    | wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
    | (wp_func_call; wp_call)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  -- translated initializer of ErrInvalid))
  -- translated initializer of ErrPermission))
  -- translated initializer of ErrExist))
  -- translated initializer of ErrNotExist))
  -- translated initializer of ErrClosed))
  -- translated initializer of ErrNoDeadline))
  -- translated initializer of ErrDeadlineExceeded))
  -- translated initializer of ErrProcessDone))
  -- translated initializer of errProcessReleased))
  -- translated initializer of ErrNoHandle))
  -- translated initializer of Interrupt))
  -- translated initializer of Kill))
  -- Stdin: its trusted initializer
  try wp_call
  -- Stdout: its trusted initializer
  try wp_call
  -- Stderr: its trusted initializer
  wp_apply wp_Stderr_init as ⟨%stderr, HStderr⟩
  repeat (first
    | wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
    | (set_option maxRecDepth 20000 in
       wp_apply _root_.Perennial.sync.wp_OnceValue as %_ -)
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  -- translated initializer of errWriteAtInAppendMode))
  -- translated initializer of errPathEscapes))
  -- translated initializer of checkWrapErr))
  -- translated initializer of checkPidfdOnce))
  -- translated initializer of errPatternHasSeparator))
  -- translated initializer of pollCopyFileRange))
  -- translated initializer of pollSplice))
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  repeat (first
    | wp_apply _root_.Perennial.errors.wp_New_errorString as %_ #_
    | (set_option maxRecDepth 20000 in wp_apply _root_.Perennial.sync.wp_OnceValue as %_ -)
    | (wp_func_call; wp_apply wp_runtime_args_impl as %_ ⟨%_, _, _⟩)
    | wp_auto)
  -- translated initializer of _root_.Perennial.io.fs.ErrClosed))
  -- translated initializer of _root_.Perennial.io.fs.ErrNotExist))
  -- translated initializer of _root_.Perennial.io.fs.ErrExist))
  -- translated initializer of _root_.Perennial.io.fs.ErrPermission))
  -- translated initializer of _root_.Perennial.io.fs.ErrInvalid))
  ipersist HStderr
  ipersist HErrExist
  ipersist HErrNotExist
  ipersist HErrInvalid
  ipersist HErrClosed
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.os get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.os }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end os

end init

end Perennial
