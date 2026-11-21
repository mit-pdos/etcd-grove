/-
Package initialization of `go_etcd_io.etcd.pkg.v3.ioutil`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`ioutilInit`, `PkgInit.lean`): `defaultBufferBytes` holds `128 * 1024`, read-only for
good. Its initializer stores that value and runs the translated initializers of its other variables,
`ErrShortRead` and `ErrExpectEOF` (`readcloser.go`: `fmt.Errorf` without verbs, whose trusted model is
`errors.New(format)`; until 2026-11-19 untranslated, `opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.ioutil.PkgInit
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import Perennial.Proof.errors.NewVar
public import Proof.fmt.OutLemmas
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
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

namespace go_etcd_io.etcd.pkg.v3.ioutil

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.pkg.v3.ioutil get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrExpectEOF _ as HErrExpectEOF
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrShortRead _ as HErrShortRead
  wp_apply wp_GlobalAlloc (V := w64) defaultBufferBytes _ as HdefaultBufferBytes
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.verify.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of defaultBufferBytes))
  -- translated initializer of ErrShortRead))
  try wp_auto
  -- `fmt.Errorf("ioutil: short read")`: no verb, Go returns `errors.New` of the format
  wp_apply (EtcdGrove.fmt.wp_Errorf_noPct _ _ (by decide)) $$ [] as %xErrShortRead ⟨#MErrShortRead, -⟩
  · iframe #; iapply ownSlice_nil
  -- translated initializer of ErrExpectEOF))
  try wp_auto
  -- `fmt.Errorf("ioutil: expect EOF")`: no verb, Go returns `errors.New` of the format
  wp_apply (EtcdGrove.fmt.wp_Errorf_noPct _ _ (by decide)) $$ [] as %xErrExpectEOF ⟨#MErrExpectEOF, -⟩
  · iframe #; iapply ownSlice_nil
  ipersist HdefaultBufferBytes
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.pkg.v3.ioutil get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.pkg.v3.ioutil

end init

end Perennial
