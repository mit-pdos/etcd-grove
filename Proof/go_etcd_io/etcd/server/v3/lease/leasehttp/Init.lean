/-
Package initialization of `go_etcd_io.etcd.server.v3.lease.leasehttp`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`lease/leasehttp/Base.lean`): `LeasePrefix` holds some string. Its initializer
runs its variables' untranslated initializers (`http.go`); the trust-boundary axiom
`LeasePrefix_init` states the one the fact reads (`"/leases"`, its value not stated),
`opaqueInitsOk` the others.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.leasehttp.Base
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
namespace go_etcd_io.etcd.server.v3.lease.leasehttp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.lease.leasehttp`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([LeaseInternalPrefix.init,
        applyTimeout.init,
        ErrLeaseHTTPTimeout.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `LeasePrefix = "/leases"` (`http.go`): some string. -/
axiom LeasePrefix_init :
    {{ (True : IProp GF) }} (App (Val LeasePrefix.init) (Val #()))
    {{ RET #(); ∃ p : GoString, globalAddr LeasePrefix ↦ p }}

end go_etcd_io.etcd.server.v3.lease.leasehttp
end opaqueInits

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
  wp_apply LeasePrefix_init as ⟨%pLeasePrefix, HLeasePrefix⟩
  wp_apply (opaqueInitsOk LeaseInternalPrefix.init (by mem_tac))
  wp_apply (opaqueInitsOk applyTimeout.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrLeaseHTTPTimeout.init (by mem_tac))
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
