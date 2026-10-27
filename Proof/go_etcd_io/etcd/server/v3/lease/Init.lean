/-
Package initialization of `go_etcd_io.etcd.server.v3.lease`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`leaseInit`, `Base.lean`): the error variables `ErrLeaseNotFound`,
`ErrLeaseExists`, `ErrLeaseTTLTooLarge` (translated `errors.New` calls: leaf pointer errors
without `Is`, by `EtcdGrove.ErrorStringLeaf`, whose `Error()` returns), `forever` (the zero
`time.Time`), the counters `leaseGranted`, `leaseRevoked` and the histogram `leaseTotalTTLs`
(`metrics.go`, untranslated: the trust-boundary axioms `<X>_init`); `opaqueInitsOk` states the
other untranslated initializers run.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.container.heap.Init
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.version.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.leasepb.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.Init
public import Proof.go_uber_org.zap.Init
public import Proof.errors.NewVarCell
public import Perennial.Proof.context.NewErrorString
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
namespace go_etcd_io.etcd.server.v3.lease
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.lease`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([defaultLeaseRevokeRate.init,
        leaseCheckpointRate.init,
        defaultLeaseCheckpointInterval.init,
        maxLeaseCheckpointBatchSize.init,
        defaultExpiredleaseRetryInterval.init,
        ErrNotPrimary.init,
        leaseRenewed.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.lease`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `leaseGranted = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`, whose `Inc` returns. -/
axiom leaseGranted_init :
    {{ (True : IProp GF) }} (App (Val leaseGranted.init) (Val #()))
    {{ RET #(); ∃ c : GoInterfaceOk, globalAddr leaseGranted ↦ GoInterface.ok c ∗ counterSpec c }}

/-- `leaseRevoked = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`, whose `Inc` returns. -/
axiom leaseRevoked_init :
    {{ (True : IProp GF) }} (App (Val leaseRevoked.init) (Val #()))
    {{ RET #(); ∃ c : GoInterfaceOk, globalAddr leaseRevoked ↦ GoInterface.ok c ∗ counterSpec c }}

/-- `leaseTotalTTLs = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom leaseTotalTTLs_init :
    {{ (True : IProp GF) }} (App (Val leaseTotalTTLs.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr leaseTotalTTLs ↦ GoInterface.ok h ∗ go_etcd_io.etcd.server.v3.storage.backend.histSpec h }}

end go_etcd_io.etcd.server.v3.lease
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.lease.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace go_etcd_io.etcd.server.v3.lease

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.lease get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLeaseTTLTooLarge _ as HErrLeaseTTLTooLarge
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLeaseExists _ as HErrLeaseExists
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLeaseNotFound _ as HErrLeaseNotFound
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.time.Time) forever _ as Hforever
  wp_apply (_root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.version.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.github_com.Masterminds.semver.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.container.heap.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.schema.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.lease.leasepb.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of forever))
  wp_apply (opaqueInitsOk defaultLeaseRevokeRate.init (by mem_tac))
  wp_apply (opaqueInitsOk leaseCheckpointRate.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultLeaseCheckpointInterval.init (by mem_tac))
  wp_apply (opaqueInitsOk maxLeaseCheckpointBatchSize.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultExpiredleaseRetryInterval.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrNotPrimary.init (by mem_tac))
  -- translated initializer of ErrLeaseNotFound))
  -- translated initializer of ErrLeaseExists))
  -- translated initializer of ErrLeaseTTLTooLarge))
  wp_apply EtcdGrove.wp_New_errorString_cell as %xNF ⟨#MNF, #CNF⟩
  wp_apply _root_.Perennial.context.wp_New_errorString as %xEx #MEx
  wp_apply _root_.Perennial.context.wp_New_errorString as %xTL #MTL
  wp_apply leaseGranted_init as ⟨%cleaseGranted, HleaseGranted, #SleaseGranted⟩
  wp_apply leaseRevoked_init as ⟨%cleaseRevoked, HleaseRevoked, #SleaseRevoked⟩
  wp_apply (opaqueInitsOk leaseRenewed.init (by mem_tac))
  wp_apply leaseTotalTTLs_init as ⟨%hleaseTotalTTLs, HleaseTotalTTLs, #SleaseTotalTTLs⟩
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  ipersist HErrLeaseNotFound
  ipersist HErrLeaseExists
  ipersist HErrLeaseTTLTooLarge
  ipersist Hforever
  ipersist HleaseGranted
  ipersist HleaseRevoked
  ipersist HleaseTotalTTLs
  ihave #TNF := EtcdGrove.errorMsg_triple _ _ _ $$ MNF
  ihave #TEx := EtcdGrove.errorMsg_triple _ _ _ $$ MEx
  ihave #TTL := EtcdGrove.errorMsg_triple _ _ _ $$ MTL
  ihave #VNF : (EtcdGrove.errVarCell ErrLeaseNotFound go!"lease not found" : IProp GF) $$ []
  · unfold EtcdGrove.errVarCell; iexists _; iframe HErrLeaseNotFound CNF
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold leaseInit leaseErrVar
  iframe #
  dsimp only
  iframe #
  repeat (first | (isplitl []; · (ipureintro; exact EtcdGrove.errorString_leaf _)) | (ipureintro; exact EtcdGrove.errorString_leaf _))

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.lease get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.lease

end init

end Perennial
