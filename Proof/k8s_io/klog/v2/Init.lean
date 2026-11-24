/-
Package initialization of `k8s_io.klog.v2`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`klogInit`, `storage/etcd3/Base.lean`): of the global `logging`, `verbosity` holds
some level, `filterLength` is 0, `logger` and `filter` are `nil` and `skipHeaders` is false, read-only
for good. Its initializer initializes its imports, allocates `logging` (zero: it has no initializer;
the allocation gives its fields' points-tos) and runs its `init` functions (trusted no-ops,
`TrustedCode/k8s_io/klog/v2.lean`: `init.1` writes 0 to `verbosity` and `filterLength` and `false` to
`skipHeaders`, as the zero value has them; klog-leaves and klog-printf, 2026-11-23).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.go_logr.logr.Init
public import Proof.k8s_io.klog.v2.internal.buffer.Init
public import Proof.k8s_io.klog.v2.internal.serialize.Init
public import Proof.k8s_io.klog.v2.internal.severity.Init
public import Proof.runtime.Init
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
variable [package_sem : _root_.Perennial.k8s_io.klog.v2.Assumptions]

namespace k8s_io.klog.v2

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.klog.v2 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := k8s_io.klog.v2.loggingT) logging _ as Hlogging
  wp_apply (_root_.Perennial.k8s_io.klog.v2.internal.severity.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.k8s_io.klog.v2.internal.serialize.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.k8s_io.klog.v2.internal.buffer.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.runtime.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.github_com.go_logr.logr.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  -- the translated init.«1»
  wp_func_call
  wp_call
  try wp_auto
  iStructNamed Hlogging
  iStructNamed settings
  ipersist verbosity
  ipersist filterLength
  ipersist logger
  ipersist filter
  ipersist skipHeaders
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold k8s_io.apiserver.pkg.storage.etcd3.klogInit
  isplitl []
  · iexists _; iexact verbosity
  isplitl []
  · have hz : (zero_val k8s_io.klog.v2.loggingT).settings'.filterLength' = W32 0 := rfl
    rw [← hz]
    iexact filterLength
  isplitl []
  · have hz : (zero_val k8s_io.klog.v2.loggingT).settings'.logger' = null := rfl
    rw [← hz]
    iexact logger
  isplitl []
  · have hz : (zero_val k8s_io.klog.v2.loggingT).settings'.filter' = interface.nil := rfl
    rw [← hz]
    iexact filter
  · have hz : (zero_val k8s_io.klog.v2.loggingT).settings'.skipHeaders' = false := rfl
    rw [← hz]
    iexact skipHeaders

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.klog.v2 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.klog.v2

end init

end Perennial
