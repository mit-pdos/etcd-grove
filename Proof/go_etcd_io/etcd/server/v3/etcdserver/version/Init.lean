/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.version`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, allocates its variables and
runs their translated initializers (`errors.go`: `errors.New` calls; until 2026-11-19 untranslated,
`opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.PkgInit
public import Perennial.Proof.errors.Link
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
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.version.Assumptions]

namespace go_etcd_io.etcd.server.v3.etcdserver.version

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNoInflightDowngrade _ as HErrNoInflightDowngrade
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrDowngradeInProcess _ as HErrDowngradeInProcess
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalidDowngradeTargetVersion _ as HErrInvalidDowngradeTargetVersion
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrInvalidDowngradeTargetVersion))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrInvalidDowngradeTargetVersion #MErrInvalidDowngradeTargetVersion
  -- translated initializer of ErrDowngradeInProcess))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrDowngradeInProcess #MErrDowngradeInProcess
  -- translated initializer of ErrNoInflightDowngrade))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrNoInflightDowngrade #MErrNoInflightDowngrade
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.version }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.etcdserver.version

end init

end Perennial
