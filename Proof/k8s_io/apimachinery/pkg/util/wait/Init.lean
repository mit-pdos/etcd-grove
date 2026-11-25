/-
Package initialization of `k8s_io.apimachinery.pkg.util.wait`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-k8s, 2026-11-20; until then the trust-boundary axiom
`opaqueInitsOk`): `ErrWaitTimeout` (`ErrorInterrupted` of an `errors.New` error, translated),
`errWaitTimeout` and `internalClock` (empty struct literals), `RealTimer` (a method value),
`ForeverTestTimeout` (a constant product), `NeverStop` (a fresh channel), `jitterRand` (a function
value) and `var _ context.Context = channelContext{}`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.math.rand.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.k8s_io.utils.clock.Init
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
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.util.wait.Assumptions]

namespace k8s_io.apimachinery.pkg.util.wait

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.util.wait get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _) jitterRand _ as HjitterRand
  wp_apply wp_GlobalAlloc (V := _) NeverStop _ as HNeverStop
  wp_apply wp_GlobalAlloc (V := _) ForeverTestTimeout _ as HForeverTestTimeout
  wp_apply wp_GlobalAlloc (V := _) internalClock _ as HinternalClock
  wp_apply wp_GlobalAlloc (V := _) RealTimer _ as HRealTimer
  wp_apply wp_GlobalAlloc (V := _) errWaitTimeout _ as HerrWaitTimeout
  wp_apply wp_GlobalAlloc (V := _) ErrWaitTimeout _ as HErrWaitTimeout
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math.rand _root_.Perennial.math.rand.initialize'
      EtcdGrove.ExternalInit.math_rand _root_.Perennial.math.rand.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.k8s_io.utils.clock.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrWaitTimeout))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xW ⟨#_, #MW⟩
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  -- translated initializer of errWaitTimeout))
  -- translated initializer of RealTimer))
  -- translated initializer of internalClock))
  -- translated initializer of ForeverTestTimeout))
  -- translated initializer of NeverStop))
  try wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩
  try wp_auto
  -- translated initializer of jitterRand))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.util.wait get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apimachinery.pkg.util.wait

end init

end Perennial
