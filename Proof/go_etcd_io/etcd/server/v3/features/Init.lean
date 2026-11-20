/-
Package initialization of `go_etcd_io.etcd.server.v3.features`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, allocates
`DefaultEtcdServerFeatureGates` and runs its translated initializer, a map literal of
`featuregate.FeatureSpec` literals (prove-smallinits, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.Init
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
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.features.Assumptions]

namespace go_etcd_io.etcd.server.v3.features

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.features get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := Loc) DefaultEtcdServerFeatureGates _ as HDefaultEtcdServerFeatureGates
  wp_apply (_root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of DefaultEtcdServerFeatureGates))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec.ty) as %mHfg Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) go_etcd_io.etcd.pkg.v3.featuregate.Feature.ty) $$ Hfg as Hfg
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.features get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.features

end init

end Perennial
