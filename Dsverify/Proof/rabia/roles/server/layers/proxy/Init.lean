/-
Package initialization of `rabia.roles.server.layers.proxy`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.proxy.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.fmt.Link
public import Dsverify.Proof.github_com.go_redis.redis.v8.Init
public import Dsverify.Proof.github_com.rs.zerolog.Init
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Net.Proof.os.Init
public import Dsverify.Proof.rabia.internal.config.Init
public import Dsverify.Proof.rabia.internal.ledger.Init
public import Dsverify.Proof.rabia.internal.logger.Init
public import Dsverify.Proof.rabia.internal.message.Init
public import Dsverify.Proof.rabia.internal.tcp.Init
public import Dsverify.Proof.runtime.PkgInitDsv
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Init
public import Dsverify.Proof.github_com.gogo.protobuf.gogoproto.Init

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
variable [_root_.Perennial.github_com.go_redis.redis.v8.InitHyp GF]
variable [_root_.Perennial.github_com.gogo.protobuf.gogoproto.InitHyp GF]
variable [_root_.Perennial.github_com.gogo.protobuf.proto.InitHyp GF]
variable [_root_.Perennial.github_com.rs.zerolog.InitHyp GF]
variable [package_sem : _root_.Perennial.rabia.roles.server.layers.proxy.Assumptions]

namespace rabia.roles.server.layers.proxy

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.rabia.roles.server.layers.proxy get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.proxy }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.rabia.internal.tcp.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.rabia.internal.message.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.rabia.internal.logger.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.rabia.internal.ledger.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.rabia.internal.config.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.Dsv.initLb_of_spec pkg_id.github_com.rs.zerolog _root_.Perennial.github_com.rs.zerolog.initialize'
      _root_.Perennial.github_com.rs.zerolog.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.Dsv.initLb_of_spec pkg_id.github_com.go_redis.redis.v8 _root_.Perennial.github_com.go_redis.redis.v8.initialize'
      _root_.Perennial.github_com.go_redis.redis.v8.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.rabia.roles.server.layers.proxy get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.proxy }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end rabia.roles.server.layers.proxy

end init

end Perennial
