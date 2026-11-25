/-
Package initialization of `google_golang_org.grpc`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`grpcInit`, `cache/v3/Base.lean`): `EnableTracing` holds `false` for good. Its
initializer initializes its imports, allocates `EnableTracing` (`var EnableTracing bool`,
`trace.go:33` at v1.84.0: translated, no initializer, so its cell holds `false`), runs the
untranslated initializers of its other variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its three translated `init`
functions (`dialoptions.go`, `rpc_util.go`, `server.go`; phase7-inits, 2026-11-25, until then the
trust-boundary axiom `initFuncsOk`), which store function values and closures in `internal`'s hook
variables, through `internal`'s invariants (`grpc/internal/Hooks.lean`); it allocates the slices the
closures append to (`globalDialOptions`, `globalPerTargetDialOptions`, `globalServerOptions`). (Until 2026-11-19 the cell
came from the trust-boundary axiom `DefaultBackoffConfig_init`.) No translated code writes
`EnableTracing`; a program that writes it (etcd's `embed` at log level debug, grpc-proxy `--debug`)
gets no proof: it would need the cell, which `finish` makes persistent.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.time.Link
public import Proof.google_golang_org.grpc.credentials.Init
public import Proof.google_golang_org.grpc.internal.Init
public import Proof.google_golang_org.grpc.keepalive.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.google_golang_org.grpc.peer.Init
public import Proof.google_golang_org.grpc.resolver.Init
public import Proof.google_golang_org.grpc.stats.Init
public import Proof.net.Init
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
namespace google_golang_org.grpc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `google_golang_org.grpc`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([logger.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end google_golang_org.grpc
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.grpc.Assumptions]

namespace google_golang_org.grpc

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := Bool) EnableTracing _ as HEnableTracing
  wp_apply wp_GlobalAlloc (V := GoSlice) globalServerOptions _ as HglobalServerOptions
  wp_apply wp_GlobalAlloc (V := GoSlice) globalPerTargetDialOptions _ as HglobalPerTargetDialOptions
  wp_apply wp_GlobalAlloc (V := GoSlice) globalDialOptions _ as HglobalDialOptions
  wp_apply (_root_.Perennial.google_golang_org.grpc.peer.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.metadata.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.stats.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.credentials.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.net.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.resolver.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.keepalive.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.internal.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk logger.init (by mem_tac))
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  ihave #Hfi : (_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.internalInit (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd4
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.AddGlobalDialOptions
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookFunc (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.ClearGlobalDialOptions
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksFunc; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.AddGlobalPerTargetDialOptions
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookFunc (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.ClearGlobalPerTargetDialOptions
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksFunc; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.JoinDialOptions
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.DisableGlobalDialOptions
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  -- the translated init.«1»
  wp_func_call
  wp_call
  try wp_auto
  ihave #Hfi : (_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.internalInit (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd4
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.AcceptCompressors
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  -- the translated init.«2»
  wp_func_call
  wp_call
  try wp_auto
  ihave #Hfi : (_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.internalInit (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hd4
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.GetServerCredentials
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.IsRegisteredMethod
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.ServerFromContext
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.AddGlobalServerOptions
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookFunc (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.ClearGlobalServerOptions
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksFunc; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.JoinServerOptions
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  wp_apply (EtcdGrove.grpcInternal.wp_store_hookAny (hG := hG) _root_.Perennial.google_golang_org.grpc.internal.XDSFilterWrapperOption
      (by unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hooksAny; mem_tac) _ _ _) $$ [Hfi Hown] as Hown
  · iframe Hown Hfi
  try wp_auto
  ipersist HEnableTracing
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.grpc get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.grpc

end init

end Perennial
