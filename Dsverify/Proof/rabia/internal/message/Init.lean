/-
Package initialization of `rabia.internal.message`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Dsverify.Proof.rabia.internal.message.Base
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.math.bits.Link
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Dsverify.Proof.bufio.Init
public import Dsverify.Proof.github_com.gogo.protobuf.gogoproto.Init
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Init
public import Dsverify.Proof.runtime.PkgInitDsv

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
variable [package_sem : _root_.Perennial.rabia.internal.message.Assumptions]

namespace rabia.internal.message

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.rabia.internal.message get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := TODO) ErrUnexpectedEndOfGroupMessage _ as HErrUnexpectedEndOfGroupMessage
  wp_apply wp_GlobalAlloc (V := TODO) ErrIntOverflowMessage _ as HErrIntOverflowMessage
  wp_apply wp_GlobalAlloc (V := TODO) ErrInvalidLengthMessage _ as HErrInvalidLengthMessage
  wp_apply wp_GlobalAlloc (V := TODO) fileDescriptor_33c57e4bae7b9afd _ as HfileDescriptor_33c57e4bae7b9afd
  wp_apply wp_GlobalAlloc (V := TODO) xxx_messageInfo_Msg _ as Hxxx_messageInfo_Msg
  wp_apply wp_GlobalAlloc (V := TODO) xxx_messageInfo_ConsensusObj _ as Hxxx_messageInfo_ConsensusObj
  wp_apply wp_GlobalAlloc (V := TODO) xxx_messageInfo_Command _ as Hxxx_messageInfo_Command
  wp_apply wp_GlobalAlloc (V := TODO) MsgType_value _ as HMsgType_value
  wp_apply wp_GlobalAlloc (V := TODO) MsgType_name _ as HMsgType_name
  wp_apply wp_GlobalAlloc (V := TODO) errFrameTooLarge _ as HerrFrameTooLarge
  wp_apply wp_GlobalAlloc (V := TODO) errFrameTooLong _ as HerrFrameTooLong
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.reflect _root_.Perennial.reflect.initialize'
      EtcdGrove.ExternalInit.reflect _root_.Perennial.reflect.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.Dsv.initLb_of_spec pkg_id.math.bits _root_.Perennial.math.bits.initialize'
      _root_.Perennial.math.bits.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.github_com.gogo.protobuf.proto.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.github_com.gogo.protobuf.gogoproto.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.bufio.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of errFrameTooLong))
  -- translated initializer of errFrameTooLarge))
  -- translated initializer of MsgType_name))
  -- translated initializer of MsgType_value))
  -- translated initializer of fileDescriptor_33c57e4bae7b9afd))
  -- translated initializer of ErrInvalidLengthMessage))
  -- translated initializer of ErrIntOverflowMessage))
  -- translated initializer of ErrUnexpectedEndOfGroupMessage))
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  -- the translated init.«1»
  wp_func_call
  wp_call
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.rabia.internal.message get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end rabia.internal.message

end init

end Perennial
