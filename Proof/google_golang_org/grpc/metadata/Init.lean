/-
Package initialization of `google_golang_org.grpc.metadata`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates `loggableMetadataKeys`, initializes its imports, runs
its variable's translated initializer, a map literal of the keys `MD.String` prints (prove-grpcext,
2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`), and its untranslated `init` function
(it sets `internal.FromOutgoingContextRaw`, another package's variable), which the trust-boundary
axiom `initFuncsOk` says returns.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.strings.Link
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
namespace google_golang_org.grpc.metadata
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `google_golang_org.grpc.metadata`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end google_golang_org.grpc.metadata
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.grpc.metadata.Assumptions]

namespace google_golang_org.grpc.metadata

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.metadata get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := Loc) loggableMetadataKeys _ as HloggableMetadataKeys
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of loggableMetadataKeys))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string go.bool) as %mHlk Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hlk as Hlk
  try wp_auto
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.metadata get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.grpc.metadata

end init

end Perennial
