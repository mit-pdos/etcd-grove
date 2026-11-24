/-
Package initialization of `go_opentelemetry_io.otel.propagation`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-misc, 2026-11-20): the interface assertions (`var _
TextMapCarrier = MapCarrier{}`, ...) and `versionPart = fmt.Sprintf("%.2X", supportedVersion)`
(Perennial's `fmt.wp_Sprintf` of the real `Sprintf`, `fmt-stage15`'s `%.P`: some string, no panic).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.sync.Link
public import Proof.net.http.Init
public import Proof.fmt.SprintfPure
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
variable [package_sem : _root_.Perennial.go_opentelemetry_io.otel.propagation.Assumptions]

namespace go_opentelemetry_io.otel.propagation

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_opentelemetry_io.otel.propagation get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.propagation }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoString) versionPart _ as HversionPart
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.Once) handleExtractErrOnce _ as HhandleExtractErrOnce
  wp_apply (_root_.Perennial.net.http.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of versionPart))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mmc -
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) go.string (go.GoType.SliceType go.string)) as %mhc1 -
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice) go.string (go.GoType.SliceType go.string)) as %mhc2 -
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %svp ⟨Svp, -⟩
  try wp_auto
  wp_apply EtcdGrove.fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"%.2X" [.prec 2 _root_.Perennial.fmt.verb_X] _ _ _ _ (by fmt_encode) (by fmt_fits) (.int _ _ _ _ (.int _) .nil) $$ [$Svp] as %rvp -
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_opentelemetry_io.otel.propagation get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.propagation }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_opentelemetry_io.otel.propagation

end init

end Perennial
