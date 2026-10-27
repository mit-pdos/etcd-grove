/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.cachekv`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.cache.v3.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_uber_org.zap.Init
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
variable [package_sem : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]
variable [EtcdGrove.ErrorStringLeaf]
variable [EtcdGrove.RpctypesEtcdErrorMethods]
variable [_root_.Perennial.fmt.Assumptions]
variable [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]
variable [_root_.Perennial.log.NewModel]

namespace github_com.mit_pdos.etcd_grove.examples.cachekv

theorem wp_initialize'_res (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv get_is_pkg_init) :
    {{ EtcdGrove.ownInitRes get_is_pkg_init pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read (EtcdGrove.read.readRegPerm (GF := GF)) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitRes get_is_pkg_init pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read (EtcdGrove.read.readRegPerm (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_res (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.common.wp_initialize'_res _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.client.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.cache.v3.wp_initialize'_lb _ Hinit.2.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize'_lb _ Hinit.2.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.2.2.1))
    $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.1))
    $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initRes_carry _ _ _ _ _ (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1))
    $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form with the resource (decision D16), from `wp_initialize'_res`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init ∗ EtcdGrove.read.readRegPerm (GF := GF) }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv }} :=
  EtcdGrove.wp_init_of_res _ _ _ _ _ (wp_initialize'_res get_is_pkg_init Hinit)


end github_com.mit_pdos.etcd_grove.examples.cachekv

end init

end Perennial
