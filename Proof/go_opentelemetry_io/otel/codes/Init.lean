/-
Package initialization of `go_opentelemetry_io.otel.codes`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates its variables and runs their translated
initializers, the map literals `codeToStr` and `strToCode` (prove-smallinits, 2026-11-20; until then
the trust-boundary axiom `opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
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
variable [package_sem : _root_.Perennial.go_opentelemetry_io.otel.codes.Assumptions]

namespace go_opentelemetry_io.otel.codes

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_opentelemetry_io.otel.codes get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.codes }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := Loc) strToCode _ as HstrToCode
  wp_apply wp_GlobalAlloc (V := Loc) codeToStr _ as HcodeToStr
  -- translated initializer of codeToStr))
  try wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := GoString) go_opentelemetry_io.otel.codes.Code.ty go.string) as %mHcs Hcs
  try wp_auto
  wp_apply (wp_mapInsert (K := w32) (V := GoString) go_opentelemetry_io.otel.codes.Code.ty) $$ Hcs as Hcs
  try wp_auto
  wp_apply (wp_mapInsert (K := w32) (V := GoString) go_opentelemetry_io.otel.codes.Code.ty) $$ Hcs as Hcs
  try wp_auto
  wp_apply (wp_mapInsert (K := w32) (V := GoString) go_opentelemetry_io.otel.codes.Code.ty) $$ Hcs as Hcs
  try wp_auto
  -- translated initializer of strToCode))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w32) go.string go_opentelemetry_io.otel.codes.Code.ty) as %mHsc Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_opentelemetry_io.otel.codes get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.codes }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_opentelemetry_io.otel.codes

end init

end Perennial
