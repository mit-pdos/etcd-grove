/-
Package initialization of `github_com.imdea_software.swiftpaxos_epaxos.replica`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, allocates its two error
variables and runs their translated initializers (`quorum.go`: `errors.New` calls).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Base
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Dsverify.Proof.bufio.Init
public import Dsverify.Proof.encoding.json.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.config.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.dlog.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.defs.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.rpc.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.state.Init
public import Net.Proof.net.Init
public import Net.Proof.os.Init
public import Perennial.Proof.errors.NewVar
public import Net.Proof.runtime.PkgInitExt

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
variable [package_sem : _root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.replica.Assumptions]
variable [_root_.Perennial.encoding.json.InitHyp GF]

namespace github_com.imdea_software.swiftpaxos_epaxos.replica

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) THREE_QUARTERS _ as HTHREE_QUARTERS
  wp_apply wp_GlobalAlloc (V := GoInterface) NO_QUORUM_FILE _ as HNO_QUORUM_FILE
  wp_apply (_root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.state.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (_root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.rpc.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.replica.defs.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (_root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.dlog.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.config.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.net.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.encoding.json.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.bufio.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of NO_QUORUM_FILE))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xNO_QUORUM_FILE ⟨#_, #MNO_QUORUM_FILE⟩
  -- translated initializer of THREE_QUARTERS))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xTHREE_QUARTERS ⟨#_, #MTHREE_QUARTERS⟩
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.imdea_software.swiftpaxos_epaxos.replica

end init

end Perennial
