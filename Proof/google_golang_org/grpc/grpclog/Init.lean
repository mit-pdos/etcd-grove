/-
Package initialization of `google_golang_org.grpc.grpclog`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`grpclogInit`, `cache/v3/Base.lean`; phase7-inits batch 2, 2026-11-25, until then
`True`): `cache` holds a map for good, whose contents are in an init-time invariant (`initInv`), for
`Component`, which package initializers call (`Spec/google_golang_org/grpc/grpclog/Component.lean`). Its
initializer initializes its imports, allocates `cache` and runs its translated initializer, an empty map
literal (prove-grpcext, 2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`), and its
untranslated `init` function (`SetLoggerV2(newLoggerV2())`), which the trust-boundary axiom
`initFuncsOk` says returns.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.grpc.grpclog.internal.Init
public import Proof.google_golang_org.grpc.internal.Hooks
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
namespace google_golang_org.grpc.grpclog
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `google_golang_org.grpc.grpclog`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end google_golang_org.grpc.grpclog
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.grpc.grpclog.Assumptions]

namespace google_golang_org.grpc.grpclog

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.grpclog get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.grpclog }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := Loc) cache _ as Hcache
  wp_apply (_root_.Perennial.google_golang_org.grpc.grpclog.internal.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of cache))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string (go.GoType.PointerType google_golang_org.grpc.grpclog.componentData.ty)) as %mHc Hc
  try wp_auto
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  ipersist Hcache
  imod (EtcdGrove.grpcInternal.initInv_alloc (hG := hG) _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.grpclog.cacheN ⊤ iprop(∃ M : GMap GoString Loc, (mHc ↦$ M : IProp GF))) $$ [Hc] with ⟨%γC, #HC⟩
  · inext; iexists _; iexact Hc
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try imodintro
  unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.grpclog.grpclogInit
  iexists mHc, γC
  iframe #

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.grpclog get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.grpclog }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.grpc.grpclog

end init

end Perennial
