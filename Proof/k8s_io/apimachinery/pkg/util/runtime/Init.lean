/-
Package initialization of `k8s_io.apimachinery.pkg.util.runtime`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`): `ReallyCrash` (`true`), `PanicHandlers` and `ErrorHandlers` (slice literals of
function values, one the closure `backoffError` returns, translated: it allocates a
`rudimentaryErrorBackoff` stamped with `time.Now()`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link
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
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.util.runtime.Assumptions]

namespace k8s_io.apimachinery.pkg.util.runtime

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.util.runtime get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.runtime }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _) ErrorHandlers _ as HErrorHandlers
  wp_apply wp_GlobalAlloc (V := _) PanicHandlers _ as HPanicHandlers
  wp_apply wp_GlobalAlloc (V := _) ReallyCrash _ as HReallyCrash
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ReallyCrash))
  -- translated initializer of PanicHandlers))
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sp -
  try wp_auto
  -- translated initializer of ErrorHandlers))
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  try wp_auto
  repeat (wp_alloc_anon; try wp_auto)
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %se -
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.util.runtime get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.runtime }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apimachinery.pkg.util.runtime

end init

end Perennial
