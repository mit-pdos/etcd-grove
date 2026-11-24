/-
Package initialization of `go_etcd_io.etcd.server.v3.lease.leasehttp`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`lease/leasehttp/Base.lean`): `LeasePrefix` holds some string. Its initializer
sets the translated `LeasePrefix` (`"/leases"`) and `LeaseInternalPrefix` (`http.go`; until
2026-11-19 the trust-boundary axiom `LeasePrefix_init`), and (prove-errinits, 2026-11-19) its other
variables, `applyTimeout` (`time.Second`) and `ErrLeaseHTTPTimeout` (`errors.New`), translated (until
then `opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.leasehttp.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.time.Link
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
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.lease.leasehttp.Assumptions]

namespace go_etcd_io.etcd.server.v3.lease.leasehttp

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLeaseHTTPTimeout _ as HErrLeaseHTTPTimeout
  wp_apply wp_GlobalAlloc (V := w64) applyTimeout _ as HapplyTimeout
  wp_apply wp_GlobalAlloc (V := GoString) LeaseInternalPrefix _ as HLeaseInternalPrefix
  wp_apply wp_GlobalAlloc (V := GoString) LeasePrefix _ as HLeasePrefix
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of LeasePrefix))
  -- translated initializer of LeaseInternalPrefix))
  -- translated initializer of applyTimeout))
  -- translated initializer of ErrLeaseHTTPTimeout))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrLeaseHTTPTimeout ⟨#_, #MErrLeaseHTTPTimeout⟩
  ipersist HLeasePrefix
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasehttp }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.lease.leasehttp

end init

end Perennial
