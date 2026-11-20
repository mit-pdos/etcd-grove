/-
Package initialization of `k8s_io.apimachinery.pkg.api.errors`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers: `var _ error = &StatusError{}` and `knownReasons`, a map literal of the
19 known reasons (prove-k8s, 2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.fmt.Link
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.net.http.Init
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
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.api.errors.Assumptions]

namespace k8s_io.apimachinery.pkg.api.errors

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.api.errors get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := Loc) knownReasons _ as HknownReasons
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.schema.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.net.http.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of knownReasons))
  try wp_auto
  wp_alloc_anon
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty (go.GoType.StructType [])) as %mHkr Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Unit) k8s_io.apimachinery.pkg.apis.«meta».v1.StatusReason.ty) $$ Hkr as Hkr
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.api.errors get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apimachinery.pkg.api.errors

end init

end Perennial
