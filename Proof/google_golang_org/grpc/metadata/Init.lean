/-
Package initialization of `google_golang_org.grpc.metadata`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates `loggableMetadataKeys`, initializes its imports, runs
its variable's translated initializer, a map literal of the keys `MD.String` prints (prove-grpcext,
2026-11-20; until then the trust-boundary axiom `opaqueInitsOk`), and its translated `init` function
(phase7-inits, 2026-11-25, first phase 7 S2 core; until then the trust-boundary axiom `initFuncsOk`),
which stores `fromOutgoingContextRaw`, converted to `any`, in `internal.FromOutgoingContextRaw`, another
package's variable: through `internal`'s invariants, lending the initializer's package state
(`grpc/internal/Hooks.lean`, `wp_store_hookAny`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.strings.Link
public import Proof.google_golang_org.grpc.internal.Init
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
  wp_apply (_root_.Perennial.google_golang_org.grpc.internal.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
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
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  ihave #Hfi : (_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.internalInit (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd3
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.FromOutgoingContextRaw
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
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
