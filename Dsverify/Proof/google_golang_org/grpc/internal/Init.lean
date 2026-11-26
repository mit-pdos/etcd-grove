/-
Package initialization of `google_golang_org.grpc.internal`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`internalInit`, `Base.lean`): the invariant of its hook cell `CanonicalString`
(`hookCell`, `Proof/runtime/InitInv.lean`), which `codes`' initializer, holding its package state, opens
for a plain store. Its initializer initializes its import `time`, allocates its translated variables
(`CanonicalString`, no initializer, so `nil`; the others with their initializers: constants, a constant
product and function literals), stores their initial values and puts `CanonicalString`'s cell in its
invariant (dsv-retire-2, 2026-11-25; until then names only, its `wp_initialize'` a trust-boundary
axiom); its other variables are names only.
-/
module

public import Dsverify.Proof.google_golang_org.grpc.internal.Base
public import Perennial.Proof.time.Link
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
  wp_apply wp_GlobalAlloc (V := GoFunc) AsyncReporterCleanupDelegate _ as HAsyncReporterCleanupDelegate
  wp_apply wp_GlobalAlloc (V := GoFunc) NewStreamWaitingForResolver _ as HNewStreamWaitingForResolver
  wp_apply wp_GlobalAlloc (V := GoFunc) TimeAfterFunc _ as HTimeAfterFunc
  wp_apply wp_GlobalAlloc (V := Bool) UserSetDefaultScheme _ as HUserSetDefaultScheme
  wp_apply wp_GlobalAlloc (V := GoString) GRPCResolverSchemeExtraMetadata _ as HGRPCResolverSchemeExtraMetadata
  wp_apply wp_GlobalAlloc (V := GoInterface) CanonicalString _ as HCanonicalString
  wp_apply wp_GlobalAlloc (V := w64) KeepaliveMinServerPingTime _ as HKeepaliveMinServerPingTime
  wp_apply wp_GlobalAlloc (V := w64) KeepaliveMinPingTime _ as HKeepaliveMinPingTime
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of KeepaliveMinPingTime))
  -- translated initializer of KeepaliveMinServerPingTime))
  -- translated initializer of GRPCResolverSchemeExtraMetadata))
  -- translated initializer of UserSetDefaultScheme))
  -- translated initializer of TimeAfterFunc))
  -- translated initializer of NewStreamWaitingForResolver))
  -- translated initializer of AsyncReporterCleanupDelegate))
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoInterface) ⊤ _ _) $$ HCanonicalString with #CCanonicalString
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try imodintro
  unfold _root_.Perennial.google_golang_org.grpc.internal.internalInit
  iexact CCanonicalString

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
