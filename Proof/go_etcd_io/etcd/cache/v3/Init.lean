/-
Package initialization of `go_etcd_io.etcd.cache.v3`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`cacheInit`, `Base.lean`; 2026-10-20, cachekv): the error variables `ErrUnsupportedRequest`,
`ErrKeyRangeInvalid`, `ErrCacheTimeout` (translated `errors.New` calls, whose `Error()` returns
their message) and `ErrNotReady` (a translated `fmt.Errorf` call), each a fixed non-nil error,
the first two with `errorStringSpec`. Its initializer allocates them, initializes its imports and
runs their translated initializers.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.k8s_io.utils.third_party.forked.golang.btree.initialize
public import Perennial.Proof.context.NewErrorString
public import Proof.fmt.Link
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.cache.v3.Assumptions]
variable [_root_.Perennial.fmt.Assumptions]
variable [EtcdGrove.RpctypesEtcdErrorMethods]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace go_etcd_io.etcd.cache.v3

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.cache.v3 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNotReady _ as HErrNotReady
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCacheTimeout _ as HErrCacheTimeout
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrKeyRangeInvalid _ as HErrKeyRangeInvalid
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnsupportedRequest _ as HErrUnsupportedRequest
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.k8s_io.utils.third_party.forked.golang.btree _root_.Perennial.k8s_io.utils.third_party.forked.golang.btree.initialize'
      EtcdGrove.ExternalInit.k8s_io_utils_third_party_forked_golang_btree _root_.Perennial.EtcdGrove.btree.initialize.wp_proof _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrUnsupportedRequest))
  -- translated initializer of ErrKeyRangeInvalid))
  -- translated initializer of ErrCacheTimeout))
  -- translated initializer of ErrNotReady))
  wp_apply _root_.Perennial.context.wp_New_errorString as %xUR #MUR
  wp_apply _root_.Perennial.context.wp_New_errorString as %xKR #MKR
  wp_apply _root_.Perennial.context.wp_New_errorString as %xCT #MCT
  wp_apply (EtcdGrove.fmt.wp_Errorf go!"cache: store not ready" slice.nil [] (DFrac.own 1))
      $$ [] as %eNR -
  · isplitl
    · iapply ownSlice_nil
    unfold EtcdGrove.fmt.argsOk; itrivial
  ipersist HErrUnsupportedRequest
  ipersist HErrKeyRangeInvalid
  ipersist HErrCacheTimeout
  ipersist HErrNotReady
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold cacheInit
  isplitr; · iexists _; iexact HErrNotReady
  isplitr; · iexists _; iexact HErrUnsupportedRequest
  isplitr; · iexists _; iexact HErrKeyRangeInvalid
  isplitr; · iexists _; iexact HErrCacheTimeout
  isplitr
  · iintro !> %e #He
    icombine HErrKeyRangeInvalid He gives %Heq
    simp only [interface.mkOk, GoInterface.ok.injEq] at Heq
    subst Heq
    iapply (errorStringSpec_of_msg _ go!"cache: invalid or out‑of‑range key range")
    iexact MKR
  iintro !> %e #He
  icombine HErrUnsupportedRequest He gives %Heq
  simp only [interface.mkOk, GoInterface.ok.injEq] at Heq
  subst Heq
  iapply (errorStringSpec_of_msg _ go!"cache: unsupported request parameters")
  iexact MUR

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.cache.v3 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.cache.v3

end init

end Perennial
