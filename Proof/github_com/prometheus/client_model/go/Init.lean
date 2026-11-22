/-
Package initialization of `github_com.prometheus.client_model.go`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Proof.github_com.prometheus.client_model.go.PkgInit
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
namespace github_com.prometheus.client_model.go
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `github_com.prometheus.client_model.go`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([MetricType_name.init,
        MetricType_value.init,
        file_io_prometheus_client_metrics_proto_rawDesc.init,
        file_io_prometheus_client_metrics_proto_rawDescData.init,
        file_io_prometheus_client_metrics_proto_enumTypes.init,
        file_io_prometheus_client_metrics_proto_msgTypes.init,
        file_io_prometheus_client_metrics_proto_goTypes.init,
        file_io_prometheus_client_metrics_proto_depIdxs.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `github_com.prometheus.client_model.go`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end github_com.prometheus.client_model.go
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.prometheus.client_model.go.Assumptions]

namespace github_com.prometheus.client_model.go

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.prometheus.client_model.go get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_model.go }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk MetricType_name.init (by mem_tac))
  wp_apply (opaqueInitsOk MetricType_value.init (by mem_tac))
  wp_apply (opaqueInitsOk file_io_prometheus_client_metrics_proto_rawDesc.init (by mem_tac))
  wp_apply (opaqueInitsOk file_io_prometheus_client_metrics_proto_rawDescData.init (by mem_tac))
  wp_apply (opaqueInitsOk file_io_prometheus_client_metrics_proto_enumTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_io_prometheus_client_metrics_proto_msgTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_io_prometheus_client_metrics_proto_goTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_io_prometheus_client_metrics_proto_depIdxs.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.prometheus.client_model.go get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_model.go }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.prometheus.client_model.go

end init

end Perennial
