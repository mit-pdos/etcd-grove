/-
Package initialization of `k8s_io.apiserver.pkg.storage.etcd3.metrics`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`metricsInit`, `storage/etcd3/Base.lean`): `ErrTransactionConflict` holds an
`errors.New("transaction conflict")` error (`EtcdGrove.errorsNewVar`). Its initializer runs its
variables' initializers (`metrics.go`): the one the fact reads translated (an `errors.New` call,
`metrics.go:42` at the apiserver pin `9c4ec15b8038`; until 2026-11-19 the trust-boundary axiom
`errorsNewVarsInit`), the others untranslated (`opaqueInitsOk`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.errors.Link
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.component_base.metrics.Init
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

section opaqueInits
namespace k8s_io.apiserver.pkg.storage.etcd3.metrics
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.apiserver.pkg.storage.etcd3.metrics`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([etcdRequestLatency.init,
        etcdRequestCounts.init,
        etcdRequestErrorCounts.init,
        objectCounts.init,
        resourceSizeEstimateDesc.init,
        resourceSizeEstimate.init,
        resourceObjectsDesc.init,
        newObjectCounts.init,
        storageSizeDescription.init,
        storageMonitor.init,
        etcdEventsReceivedCounts.init,
        etcdBookmarkCounts.init,
        etcdBookmarkTotal.init,
        etcdLeaseObjectCounts.init,
        decodeErrorCounts.init,
        listLatency.init,
        sinceInSeconds.init,
        «_».init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end k8s_io.apiserver.pkg.storage.etcd3.metrics
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.metrics.Assumptions]

namespace k8s_io.apiserver.pkg.storage.etcd3.metrics

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTransactionConflict _ as HErrTransactionConflict
  wp_apply (_root_.Perennial.k8s_io.component_base.metrics.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.schema.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrTransactionConflict))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrTransactionConflict ⟨#MErrTransactionConflictc, #MErrTransactionConflict⟩
  wp_apply (opaqueInitsOk etcdRequestLatency.init (by mem_tac))
  wp_apply (opaqueInitsOk etcdRequestCounts.init (by mem_tac))
  wp_apply (opaqueInitsOk etcdRequestErrorCounts.init (by mem_tac))
  wp_apply (opaqueInitsOk objectCounts.init (by mem_tac))
  wp_apply (opaqueInitsOk resourceSizeEstimateDesc.init (by mem_tac))
  wp_apply (opaqueInitsOk resourceSizeEstimate.init (by mem_tac))
  wp_apply (opaqueInitsOk resourceObjectsDesc.init (by mem_tac))
  wp_apply (opaqueInitsOk newObjectCounts.init (by mem_tac))
  wp_apply (opaqueInitsOk storageSizeDescription.init (by mem_tac))
  wp_apply (opaqueInitsOk storageMonitor.init (by mem_tac))
  wp_apply (opaqueInitsOk etcdEventsReceivedCounts.init (by mem_tac))
  wp_apply (opaqueInitsOk etcdBookmarkCounts.init (by mem_tac))
  wp_apply (opaqueInitsOk etcdBookmarkTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk etcdLeaseObjectCounts.init (by mem_tac))
  wp_apply (opaqueInitsOk decodeErrorCounts.init (by mem_tac))
  wp_apply (opaqueInitsOk listLatency.init (by mem_tac))
  wp_apply (opaqueInitsOk sinceInSeconds.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  ipersist HErrTransactionConflict
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  unfold k8s_io.apiserver.pkg.storage.etcd3.metricsInit EtcdGrove.errorsNewVar
  iexists _
  iframe HErrTransactionConflict
  iexact MErrTransactionConflict

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apiserver.pkg.storage.etcd3.metrics

end init

end Perennial
