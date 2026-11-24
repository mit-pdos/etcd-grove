/-
Package initialization of `k8s_io.klog.v2.internal.buffer`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`klogBufferInit`, `storage/etcd3/Base.lean`): its pool `buffers` is a `sync.Pool`
whose `New` (not `nil`) allocates a `Buffer`, of `*Buffer`s owned whole. Its initializer allocates
`buffers`, initializes its imports and stores the pool's composite literal (klog-infos, 2026-11-23;
until then the variable was skipped, the package translated types only).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.sync.Link
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
variable [package_sem : _root_.Perennial.k8s_io.klog.v2.internal.buffer.Assumptions]

namespace k8s_io.klog.v2.internal.buffer

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.klog.v2.internal.buffer get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2.internal.buffer }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.sync.Pool) buffers _ as Hbuffers
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of buffers))
  rw [recv_eq_func_mk BAnon BAnon]
  try wp_auto
  imod (_root_.Perennial.sync.init_Pool (globalAddr buffers)
      { (zero_val _root_.Perennial.sync.Pool) with New' := _ } iprop(True)
      k8s_io.apiserver.pkg.storage.etcd3.klogPoolElem ⊤ (by rfl)) $$ [Hbuffers] with #Hpool
  · iframe Hbuffers
    iapply _root_.Perennial.sync.newSpec_of_true
    iright
    wp_start as -
    wp_auto
    wp_alloc lb as Hlb
    wp_auto
    iapply HΦ
    iunfold k8s_io.apiserver.pkg.storage.etcd3.klogPoolElem
    iexists lb, []
    isplitr
    · ipureintro; rfl
    iunfold k8s_io.apiserver.pkg.storage.etcd3.klogOwnBuffer
    iStructNamed Hlb
    iframe Tmp
    iapply _root_.Perennial.bytes.ownBuffer_new
    iexact Buffer
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  iunfold k8s_io.apiserver.pkg.storage.etcd3.klogBufferInit
  iexists _
  iframe Hpool
  ipureintro
  intro h; cases h

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.klog.v2.internal.buffer get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2.internal.buffer }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.klog.v2.internal.buffer

end init

end Perennial
