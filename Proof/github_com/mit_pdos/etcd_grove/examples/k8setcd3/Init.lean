/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.k8setcd3`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`drvInit`, `Base.lean`): its error variables (`k8setcd3.go`: `errNotObj`,
`errBadData`, `errBadRV`, `errNoList`, `errDeleteRejected`, `errUpdateRejected`, translated
`errors.New` calls) each hold a fixed `*errorString` whose `Error()` returns. Its initializer
allocates them, initializes its imports and runs their translated initializers.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.anishathalye.porcupine.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Init
public import Proof.go_uber_org.zap.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.apiserver.pkg.storage.Init
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Init
public import Proof.k8s_io.apiserver.pkg.storage.value.Init
public import Perennial.Proof.context.NewErrorString
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
variable [package_sem : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
variable [EtcdGrove.ErrorStringLeaf]
variable [EtcdGrove.RpctypesEtcdErrorMethods]
variable [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]
variable [_root_.Perennial.log.NewModel]

namespace github_com.mit_pdos.etcd_grove.examples.k8setcd3

theorem wp_initialize'_res (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 get_is_pkg_init) :
    {{ EtcdGrove.ownInitRes get_is_pkg_init pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read (EtcdGrove.read.readRegPerm (GF := GF)) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitRes get_is_pkg_init pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read (EtcdGrove.read.readRegPerm (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_res (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) errUpdateRejected _ as HerrUpdateRejected
  wp_apply wp_GlobalAlloc (V := GoInterface) errDeleteRejected _ as HerrDeleteRejected
  wp_apply wp_GlobalAlloc (V := GoInterface) errNoList _ as HerrNoList
  wp_apply wp_GlobalAlloc (V := GoInterface) errBadRV _ as HerrBadRV
  wp_apply wp_GlobalAlloc (V := GoInterface) errBadData _ as HerrBadData
  wp_apply wp_GlobalAlloc (V := GoInterface) errNotObj _ as HerrNotObj
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lintest.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.common.wp_initialize'_res _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.k8s_io.apiserver.pkg.storage.value.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.k8s_io.apiserver.pkg.storage.etcd3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.k8s_io.apiserver.pkg.storage.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.schema.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.client.v3.kubernetes.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.client.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.github_com.goose_lang.primitive _root_.Perennial.github_com.goose_lang.primitive.initialize'
      EtcdGrove.ExternalInit.github_com_goose_lang_primitive _root_.Perennial.github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.github_com.anishathalye.porcupine.wp_initialize'_lb _ Hinit.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.1))
    $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1))
    $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of errNotObj))
  -- translated initializer of errBadData))
  -- translated initializer of errBadRV))
  -- translated initializer of errNoList))
  -- translated initializer of errDeleteRejected))
  -- translated initializer of errUpdateRejected))
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xNO #MNO
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xBD #MBD
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xBR #MBR
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xNL #MNL
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xDR #MDR
  try wp_auto
  wp_apply _root_.Perennial.context.wp_New_errorString as %xUR #MUR
  try wp_auto
  ipersist HerrNotObj
  ipersist HerrBadData
  ipersist HerrBadRV
  ipersist HerrNoList
  ipersist HerrDeleteRejected
  ipersist HerrUpdateRejected
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold drvInit
  isplitr
  · iexists xNO
    iframe HerrNotObj
    unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.errorStringSpec
    iintro !> %Φ HΦ
    iapply MNO
    inext
    iapply HΦ
  isplitr
  · iexists xBD
    iframe HerrBadData
    unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.errorStringSpec
    iintro !> %Φ HΦ
    iapply MBD
    inext
    iapply HΦ
  isplitr
  · iexists xBR
    iframe HerrBadRV
    unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.errorStringSpec
    iintro !> %Φ HΦ
    iapply MBR
    inext
    iapply HΦ
  isplitr
  · iexists xNL
    iframe HerrNoList
    unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.errorStringSpec
    iintro !> %Φ HΦ
    iapply MNL
    inext
    iapply HΦ
  isplitr
  · iexists xDR
    iframe HerrDeleteRejected
    unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.errorStringSpec
    iintro !> %Φ HΦ
    iapply MDR
    inext
    iapply HΦ
  iexists xUR
  iframe HerrUpdateRejected
  unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.errorStringSpec
  iintro !> %Φ HΦ
  iapply MUR
  inext
  iapply HΦ

/-- Perennial's form with the resource (decision D16), from `wp_initialize'_res`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init ∗ EtcdGrove.read.readRegPerm (GF := GF) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }} :=
  EtcdGrove.wp_init_of_res _ _ _ _ _ (wp_initialize'_res get_is_pkg_init Hinit)


end github_com.mit_pdos.etcd_grove.examples.k8setcd3

end init

end Perennial
