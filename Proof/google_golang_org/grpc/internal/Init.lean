/-
Package initialization of `google_golang_org.grpc.internal`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`internalInit`, `cache/v3/Base.lean`): the invariants of its hook cells (`hookCell`),
which a package initializer holding its package state opens for a plain store (`grpc/internal/Hooks.lean`).
Its initializer allocates the hook variables that the translated `init`s of `metadata`, `codes` and grpc
set (`internal.go`, `experimental.go`: no initializers, so each holds `nil`) and puts each cell in its
invariant (phase7-inits, 2026-11-25; `FromOutgoingContextRaw` first in phase 7 S2 core, 2026-11-23); its
other variables with initializers are goose `[[skip]]`s (literals), the rest names only.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
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
variable [package_sem : _root_.Perennial.google_golang_org.grpc.internal.Assumptions]

namespace google_golang_org.grpc.internal

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.internal get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) XDSFilterWrapperOption _ as HXDSFilterWrapperOption
  wp_apply wp_GlobalAlloc (V := GoInterface) FromOutgoingContextRaw _ as HFromOutgoingContextRaw
  wp_apply wp_GlobalAlloc (V := GoInterface) JoinServerOptions _ as HJoinServerOptions
  wp_apply wp_GlobalAlloc (V := GoInterface) JoinDialOptions _ as HJoinDialOptions
  wp_apply wp_GlobalAlloc (V := GoFunc) ClearGlobalPerTargetDialOptions _ as HClearGlobalPerTargetDialOptions
  wp_apply wp_GlobalAlloc (V := GoInterface) AddGlobalPerTargetDialOptions _ as HAddGlobalPerTargetDialOptions
  wp_apply wp_GlobalAlloc (V := GoFunc) ClearGlobalDialOptions _ as HClearGlobalDialOptions
  wp_apply wp_GlobalAlloc (V := GoInterface) DisableGlobalDialOptions _ as HDisableGlobalDialOptions
  wp_apply wp_GlobalAlloc (V := GoInterface) AddGlobalDialOptions _ as HAddGlobalDialOptions
  wp_apply wp_GlobalAlloc (V := GoFunc) ClearGlobalServerOptions _ as HClearGlobalServerOptions
  wp_apply wp_GlobalAlloc (V := GoInterface) AddGlobalServerOptions _ as HAddGlobalServerOptions
  wp_apply wp_GlobalAlloc (V := GoInterface) ServerFromContext _ as HServerFromContext
  wp_apply wp_GlobalAlloc (V := GoInterface) IsRegisteredMethod _ as HIsRegisteredMethod
  wp_apply wp_GlobalAlloc (V := GoInterface) CanonicalString _ as HCanonicalString
  wp_apply wp_GlobalAlloc (V := GoInterface) GetServerCredentials _ as HGetServerCredentials
  wp_apply wp_GlobalAlloc (V := GoInterface) AcceptCompressors _ as HAcceptCompressors
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HFromOutgoingContextRaw with #CFromOutgoingContextRaw
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HCanonicalString with #CCanonicalString
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HAddGlobalDialOptions with #CAddGlobalDialOptions
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HAddGlobalPerTargetDialOptions with #CAddGlobalPerTargetDialOptions
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HJoinDialOptions with #CJoinDialOptions
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HDisableGlobalDialOptions with #CDisableGlobalDialOptions
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HAcceptCompressors with #CAcceptCompressors
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HGetServerCredentials with #CGetServerCredentials
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HIsRegisteredMethod with #CIsRegisteredMethod
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HServerFromContext with #CServerFromContext
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HAddGlobalServerOptions with #CAddGlobalServerOptions
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HJoinServerOptions with #CJoinServerOptions
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HXDSFilterWrapperOption with #CXDSFilterWrapperOption
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoFunc) ⊤ _ _) $$ HClearGlobalDialOptions with #CClearGlobalDialOptions
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoFunc) ⊤ _ _) $$ HClearGlobalPerTargetDialOptions with #CClearGlobalPerTargetDialOptions
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoFunc) ⊤ _ _) $$ HClearGlobalServerOptions with #CClearGlobalServerOptions
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try imodintro
  unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.internalInit _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksFunc
  simp only [_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hookCells]
  iframe #
  try (imodintro; itrivial)

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc.internal get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.grpc.internal

end init

end Perennial
