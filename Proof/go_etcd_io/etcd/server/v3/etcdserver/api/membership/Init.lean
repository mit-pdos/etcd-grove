/-
Package initialization of `go_etcd_io.etcd.server.v3.etcdserver.api.membership`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`membershipInit`, `etcdserver/apply/Base.lean`): `ClusterVersionMetrics` holds a
fixed pointer (a `*prometheus.GaugeVec`, with its label names: D19l (iii)), and (D43 M4,
2026-10-26) every error variable its `errors.New` error (`errorsNewVars membershipErrMsgs`). Its
initializer allocates its error variables, initializes its imports, runs their translated
initializers (`errors.go`: `errors.New` calls, Perennial's `errors.wp_New_errorString`; translated
since 2026-11-19, until then the trust-boundary axiom `errorsNewVarsInit`) and its other variables'
untranslated initializers; the trust-boundary axiom `ClusterVersionMetrics_init` states the one the
fact reads (`metrics.go`: `prometheus.NewGaugeVec(...)`), `opaqueInitsOk` the others.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.sync.Link
public import Proof.encoding.json.Init
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.Init
public import Proof.go_etcd_io.etcd.pkg.v3.notify.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.version.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
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
namespace go_etcd_io.etcd.server.v3.etcdserver.api.membership
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.membership`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([knownPeers.init,
        isLearner.init,
        StoreMembersPrefix.init,
        storeRemovedMembersPrefix.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.etcdserver.api.membership`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `ClusterVersionMetrics = prometheus.NewGaugeVec(..., []string{"cluster_version"})`
(`metrics.go`): a `*GaugeVec` with those label names (`vecLabels`). -/
axiom ClusterVersionMetrics_init :
    {{ (True : IProp GF) }} (App (Val ClusterVersionMetrics.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr ClusterVersionMetrics ↦ v ∗ ⌜EtcdGrove.prometheus.vecLabels v [go!"cluster_version"]⌝ }}

end go_etcd_io.etcd.server.v3.etcdserver.api.membership
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

namespace go_etcd_io.etcd.server.v3.etcdserver.api.membership

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTooManyLearners _ as HErrTooManyLearners
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrMemberNotLearner _ as HErrMemberNotLearner
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrPeerURLexists _ as HErrPeerURLexists
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrIDNotFound _ as HErrIDNotFound
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrIDExists _ as HErrIDExists
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrIDRemoved _ as HErrIDRemoved
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.go_etcd_io.raft.v3.raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.initialize'
      EtcdGrove.ExternalInit.go_etcd_io_raft_v3_raftpb _root_.Perennial.go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.version.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.notify.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.types.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.github_com.Masterminds.semver.v3.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.encoding.json.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrIDRemoved))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrIDRemoved #MErrIDRemoved
  -- translated initializer of ErrIDExists))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrIDExists #MErrIDExists
  -- translated initializer of ErrIDNotFound))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrIDNotFound #MErrIDNotFound
  -- translated initializer of ErrPeerURLexists))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrPeerURLexists #MErrPeerURLexists
  -- translated initializer of ErrMemberNotLearner))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrMemberNotLearner #MErrMemberNotLearner
  -- translated initializer of ErrTooManyLearners))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrTooManyLearners #MErrTooManyLearners
  wp_apply ClusterVersionMetrics_init as ⟨%vClusterVersionMetrics, HClusterVersionMetrics, #LClusterVersionMetrics⟩
  wp_apply (opaqueInitsOk knownPeers.init (by mem_tac))
  wp_apply (opaqueInitsOk isLearner.init (by mem_tac))
  wp_apply (opaqueInitsOk StoreMembersPrefix.init (by mem_tac))
  wp_apply (opaqueInitsOk storeRemovedMembersPrefix.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  ipersist HClusterVersionMetrics
  ipersist HErrIDRemoved
  ipersist HErrIDExists
  ipersist HErrIDNotFound
  ipersist HErrPeerURLexists
  ipersist HErrMemberNotLearner
  ipersist HErrTooManyLearners
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  unfold membershipInit membershipErrMsgs
  simp only [EtcdGrove.errorsNewVars, EtcdGrove.errorsNewVar]
  iframe #

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.etcdserver.api.membership

end init

end Perennial
