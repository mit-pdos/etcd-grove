/-
Package initialization of `google_golang_org.grpc.resolver`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates its two variables and runs their translated
initializers (`m = make(map[string]Builder)`, `defaultScheme = "passthrough"`, `resolver.go:38-43`),
after initializing its imports (`serviceconfig`, `attributes`: types only).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.grpc.attributes.Init
public import Proof.google_golang_org.grpc.serviceconfig.Init
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
variable [package_sem : _root_.Perennial.google_golang_org.grpc.resolver.Assumptions]

namespace google_golang_org.grpc.resolver

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.resolver get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.resolver }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoString) defaultScheme _ as HdefaultScheme
  wp_apply wp_GlobalAlloc (V := Loc) m _ as Hm
  wp_apply (_root_.Perennial.google_golang_org.grpc.serviceconfig.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.attributes.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of m))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string google_golang_org.grpc.resolver.Builder.ty) as %mb Hmb
  try wp_auto
  -- translated initializer of defaultScheme))
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.resolver get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.resolver }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.grpc.resolver

end init

end Perennial
