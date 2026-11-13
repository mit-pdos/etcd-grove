/-
Package initialization of `go_etcd_io.etcd.client.pkg.v3.fileutil`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`fileutilInit`, `PkgInit.lean`): the lock functions `linuxLockFile`/`linuxTryLockFile`
(both OFD's or both `flock`'s), the write-lock description `wrlck` and `ErrLocked` (an error whose
`Error()` returns), read-only for good. Its initializer stores `ErrLocked` (a translated `errors.New`),
`wrlck` (a struct literal) and the `flock` functions, initializes its imports and runs its translated
`init` function (lock_linux.go), which probes OFD locks with `F_OFD_GETLK` on fd 0 and switches both
functions to OFD's on success: the probe's errno is any (`syscall.FcntlFlock.wp_getlk`), so either
outcome.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.time.Link
public import LinuxFs.Proof.bufio.Init
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import LinuxFs.Proof.go_uber_org.zap.Init
public import LinuxFs.Proof.golang_org.x.sys.unix.Init
public import LinuxFs.Proof.io.fs.Init
public import LinuxFs.Proof.os.Init
public import LinuxFs.Proof.path.filepath.Init
public import LinuxFs.Proof.syscall.Init
public import Perennial.Proof.errors.NewVar
public import LinuxFs.Proof.syscall.FileOps
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
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

namespace go_etcd_io.etcd.client.pkg.v3.fileutil

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoFunc) linuxLockFile _ as HlinuxLockFile
  wp_apply wp_GlobalAlloc (V := GoFunc) linuxTryLockFile _ as HlinuxTryLockFile
  wp_apply wp_GlobalAlloc (V := syscall.Flock_t) wrlck _ as Hwrlck
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLocked _ as HErrLocked
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.golang_org.x.sys.unix.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.syscall.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.verify.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.path.filepath.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.io.fs.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.bufio.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrLocked))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xL #EL
  try wp_auto
  -- translated initializer of wrlck))
  -- translated initializer of linuxTryLockFile))
  -- translated initializer of linuxLockFile))
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  wp_apply (_root_.Perennial.EtcdGrove.syscall.FcntlFlock.wp_getlk _ _ _) $$ getlk as %e ⟨%v', Hv, %hv⟩
  try wp_auto
  ipersist Hwrlck
  ipersist HErrLocked
  ihave #Hrest : (∃ e : GoInterfaceOk, globalAddr ErrLocked ↦□ GoInterface.ok e ∗ EtcdGrove.errOk e) ∗
      (∃ w : syscall.Flock_t, globalAddr wrlck ↦□ w ∗
        ⌜w.Type' = W16 1 ∧ w.Whence' = W16 0 ∧ w.Start' = W64 0 ∧ w.Len' = W64 0⌝) $$ []
  · isplitl []
    · unfold EtcdGrove.errOk
      iexists _
      iframe HErrLocked
      iintro !> %Φ' HΦ'
      iapply EL
      inext
      iapply HΦ'
    · iexists _
      iframe Hwrlck
      ipureintro
      exact ⟨rfl, rfl, rfl, rfl⟩
  by_cases he : e = 0
  · rw [show errnoErr e = interface.nil from by unfold errnoErr; simp only [he, ↓reduceIte]]
    wp_auto
    ipersist HlinuxLockFile
    ipersist HlinuxTryLockFile
    iframe Hown
    imodintro
    isplitr
    · ipureintro
      exact isPanic_intoVal _
    is_pkg_init_finish
    imodintro
    unfold EtcdGrove.fileutil.fileutilInit
    icases Hrest with ⟨Hr1, Hr2⟩
    iframe Hr1 Hr2
    iexists true
    simp only [EtcdGrove.fileutil.lockFn, EtcdGrove.fileutil.tryLockFn, ↓reduceIte]
    iframe HlinuxLockFile HlinuxTryLockFile
  · rw [show errnoErr e = interface.mkOk syscall.Errno.ty #e from by unfold errnoErr; simp only [he, ↓reduceIte]]
    wp_auto
    ipersist HlinuxLockFile
    ipersist HlinuxTryLockFile
    iframe Hown
    imodintro
    isplitr
    · ipureintro
      exact isPanic_intoVal _
    is_pkg_init_finish
    imodintro
    unfold EtcdGrove.fileutil.fileutilInit
    icases Hrest with ⟨Hr1, Hr2⟩
    iframe Hr1 Hr2
    iexists false
    simp only [EtcdGrove.fileutil.lockFn, EtcdGrove.fileutil.tryLockFn, ↓reduceIte, Bool.false_eq_true]
    iframe HlinuxLockFile HlinuxTryLockFile

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.client.pkg.v3.fileutil

end init

end Perennial
