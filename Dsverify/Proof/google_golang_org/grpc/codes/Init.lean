/-
Package initialization of `google_golang_org.grpc.codes`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer allocates `strToCode`, initializes its import (grpc's
`internal`), runs its translated initializer, a map literal, and its translated `init` function, which
stores `canonicalString`, converted to `any`, in `internal.CanonicalString`, another package's variable:
through `internal`'s invariant, lending the initializer's package state (`EtcdGrove.grpcInternal.
wp_store_hook`). (dsv-retire-2, 2026-11-25: until then names only, its `wp_initialize'` a trust-boundary
axiom.)
-/
module

public import Dsverify.Proof.google_golang_org.grpc.codes.Base
public import Dsverify.Proof.google_golang_org.grpc.internal.Init
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
variable [package_sem : _root_.Perennial.google_golang_org.grpc.codes.Assumptions]

namespace google_golang_org.grpc.codes

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.codes get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := Loc) strToCode _ as HstrToCode
  wp_apply (_root_.Perennial.google_golang_org.grpc.internal.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of strToCode))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w32) go.string google_golang_org.grpc.codes.Code.ty) as %mHsc Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hsc as Hsc
  try wp_auto
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  ihave #Hfi : (_root_.Perennial.google_golang_org.grpc.internal.internalInit (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd1
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hook (hG := hG) (V := GoInterface) (t := go.any) _ _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown; unfold _root_.Perennial.google_golang_org.grpc.internal.internalInit; iexact Hfi
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.codes get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.grpc.codes

end init

end Perennial
