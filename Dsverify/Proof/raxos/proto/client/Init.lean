/-
Package initialization of `raxos.proto.client`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the trusted
initializers of its variables (`X.init`, models in `TrustedCode/` that do nothing).
-/
module

public import Dsverify.Proof.raxos.proto.client.Base
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.google_golang_org.protobuf.proto.Init
public import Dsverify.Proof.google_golang_org.protobuf.reflect.protoreflect.Init
public import Dsverify.Proof.google_golang_org.protobuf.runtime.protoimpl.Init
public import Dsverify.Proof.raxos.proto.Init
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
variable [package_sem : _root_.Perennial.raxos.proto.client.Assumptions]

namespace raxos.proto.client

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.raxos.proto.client get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.raxos.proto.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (_root_.Perennial.google_golang_org.protobuf.proto.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.reflect _root_.Perennial.reflect.initialize'
      EtcdGrove.ExternalInit.reflect _root_.Perennial.reflect.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.google_golang_org.protobuf.runtime.protoimpl.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.google_golang_org.protobuf.reflect.protoreflect.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_call  -- file_proto_client_client_proto_rawDesc: its trusted initializer does nothing
  wp_call  -- file_proto_client_client_proto_rawDescData: its trusted initializer does nothing
  wp_call  -- file_proto_client_client_proto_msgTypes: its trusted initializer does nothing
  wp_call  -- file_proto_client_client_proto_goTypes: its trusted initializer does nothing
  wp_call  -- file_proto_client_client_proto_depIdxs: its trusted initializer does nothing
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.raxos.proto.client get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end raxos.proto.client

end init

end Perennial
