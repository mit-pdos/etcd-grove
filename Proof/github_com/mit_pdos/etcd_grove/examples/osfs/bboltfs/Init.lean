/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`bboltfsInit`, `PkgInit.lean`): `errFailed`, `errPageSize` and `errMapTooLarge` hold
non-nil errors, read-only for good. Its initializer allocates its variables (those and `envErrors`, zero),
initializes its imports and runs its variables' translated initializers (`errors.New` calls).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.unsafe.Link
public import Proof.golang_org.x.sys.unix.Init
public import Proof.os.Init
public import Proof.syscall.Init
public import Perennial.Proof.errors.NewVar
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

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

namespace github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := w64) envErrors _ as HenvErrors
  wp_apply wp_GlobalAlloc (V := GoInterface) errMapTooLarge _ as HerrMapTooLarge
  wp_apply wp_GlobalAlloc (V := GoInterface) errFailed _ as HerrFailed
  wp_apply wp_GlobalAlloc (V := GoInterface) errPageSize _ as HerrPageSize
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.golang_org.x.sys.unix.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.«unsafe» _root_.Perennial.«unsafe».initialize'
      EtcdGrove.ExternalInit.unsafe_ _root_.Perennial.«unsafe».wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.syscall.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of errPageSize))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrPageSize ⟨#_, #MerrPageSize⟩
  -- translated initializer of errFailed))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrFailed ⟨#_, #MerrFailed⟩
  -- translated initializer of errMapTooLarge))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrMapTooLarge ⟨#_, #MerrMapTooLarge⟩
  ipersist HerrFailed
  ipersist HerrPageSize
  ipersist HerrMapTooLarge
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  unfold bboltfsInit
  iexists _, _, _
  iframe HerrFailed HerrPageSize HerrMapTooLarge
  ipureintro
  exact ⟨nofun, nofun, nofun⟩

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

end init

end Perennial
