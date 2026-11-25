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
public import Dsverify.Proof.github_com.gogo.protobuf.gogoproto.Init
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Init
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.math.bits.Link
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Proof.bufio.Init
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Spec
public import Perennial.Proof.errors.NewVar
public import Proof.fmt.OutLemmas
public import Proof.runtime.PkgInitExt
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
variable [_root_.Perennial.github_com.gogo.protobuf.gogoproto.InitHyp GF]
variable [_root_.Perennial.github_com.gogo.protobuf.proto.InitHyp GF]
variable [package_sem : _root_.Perennial.rabia.internal.message.Assumptions]
variable [_root_.Perennial.github_com.gogo.protobuf.proto.Hyps GF]

namespace rabia.internal.message

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
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
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnexpectedEndOfGroupMessage _ as HErrUnexpectedEndOfGroupMessage
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrIntOverflowMessage _ as HErrIntOverflowMessage
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrInvalidLengthMessage _ as HErrInvalidLengthMessage
  wp_apply wp_GlobalAlloc (V := GoSlice) fileDescriptor_33c57e4bae7b9afd _ as HfileDescriptor_33c57e4bae7b9afd
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.github_com.gogo.protobuf.proto.InternalMessageInfo) xxx_messageInfo_Msg _ as Hxxx_messageInfo_Msg
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.github_com.gogo.protobuf.proto.InternalMessageInfo) xxx_messageInfo_ConsensusObj _ as Hxxx_messageInfo_ConsensusObj
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.github_com.gogo.protobuf.proto.InternalMessageInfo) xxx_messageInfo_Command _ as Hxxx_messageInfo_Command
  wp_apply wp_GlobalAlloc (V := Loc) MsgType_value _ as HMsgType_value
  wp_apply wp_GlobalAlloc (V := Loc) MsgType_name _ as HMsgType_name
  wp_apply wp_GlobalAlloc (V := GoInterface) errFrameTooLarge _ as HerrFrameTooLarge
  wp_apply wp_GlobalAlloc (V := GoInterface) errFrameTooLong _ as HerrFrameTooLong
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.reflect _root_.Perennial.reflect.initialize'
      EtcdGrove.ExternalInit.reflect _root_.Perennial.reflect.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math.bits _root_.Perennial.math.bits.initialize'
      EtcdGrove.ExternalInit.math_bits _root_.Perennial.math.bits.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.github_com.gogo.protobuf.proto _root_.Perennial.github_com.gogo.protobuf.proto.initialize'
      EtcdGrove.ExternalInit.github_com_gogo_protobuf_proto _root_.Perennial.github_com.gogo.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.github_com.gogo.protobuf.gogoproto _root_.Perennial.github_com.gogo.protobuf.gogoproto.initialize'
      EtcdGrove.ExternalInit.github_com_gogo_protobuf_gogoproto _root_.Perennial.github_com.gogo.protobuf.gogoproto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
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
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrFrameTooLong ⟨#_, #MerrFrameTooLong⟩
  -- translated initializer of errFrameTooLarge))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrFrameTooLarge ⟨#_, #MerrFrameTooLarge⟩
  -- translated initializer of MsgType_name))
  try wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := GoString)) as %mName Hm
  repeat (wp_apply wp_mapInsert $$ Hm as Hm)
  -- translated initializer of MsgType_value))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w32)) as %mVal Hm2
  repeat (wp_apply wp_mapInsert $$ Hm2 as Hm2)
  -- translated initializer of fileDescriptor_33c57e4bae7b9afd))
  try wp_auto
  wp_apply wp_slice_literal (V := w8) _
  isplitr
  · ipureintro; first | rfl | (with_unfolding_all rfl) | simp | decide
  iintro %fdp ⟨Hfds, _⟩
  -- translated initializer of ErrInvalidLengthMessage))
  try wp_auto
  -- `fmt.Errorf("proto: negative length found during unmarshaling")`: no verb, Go returns `errors.New` of the format
  wp_apply (EtcdGrove.fmt.wp_Errorf_noPct _ _ (by decide)) $$ [] as %xErrInvalidLengthMessage ⟨#MErrInvalidLengthMessage, -⟩
  · iframe #; iapply ownSlice_nil
  -- translated initializer of ErrIntOverflowMessage))
  try wp_auto
  -- `fmt.Errorf("proto: integer overflow")`: no verb, Go returns `errors.New` of the format
  wp_apply (EtcdGrove.fmt.wp_Errorf_noPct _ _ (by decide)) $$ [] as %xErrIntOverflowMessage ⟨#MErrIntOverflowMessage, -⟩
  · iframe #; iapply ownSlice_nil
  -- translated initializer of ErrUnexpectedEndOfGroupMessage))
  try wp_auto
  -- `fmt.Errorf("proto: unexpected end of group")`: no verb, Go returns `errors.New` of the format
  wp_apply (EtcdGrove.fmt.wp_Errorf_noPct _ _ (by decide)) $$ [] as %xErrUnexpectedEndOfGroupMessage ⟨#MErrUnexpectedEndOfGroupMessage, -⟩
  · iframe #; iapply ownSlice_nil
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  iunfold EtcdGrove.ownInitLb at Hown
  icases Hown with ⟨%σg, Hg, #Hok, %Hle⟩
  wp_apply (_root_.Perennial.github_com.gogo.protobuf.proto.Hyps.RegisterEnum (GF := GF)) $$ [$Hg $HMsgType_value] as Hg
  try wp_auto
  wp_apply (_root_.Perennial.github_com.gogo.protobuf.proto.Hyps.RegisterType (GF := GF)) $$ [$Hg] as Hg
  try wp_auto
  wp_apply (_root_.Perennial.github_com.gogo.protobuf.proto.Hyps.RegisterType (GF := GF)) $$ [$Hg] as Hg
  try wp_auto
  wp_apply (_root_.Perennial.github_com.gogo.protobuf.proto.Hyps.RegisterType (GF := GF)) $$ [$Hg] as Hg
  try wp_auto
  -- the translated init.«1»
  wp_func_call
  wp_call
  try wp_auto
  wp_apply (_root_.Perennial.github_com.gogo.protobuf.proto.Hyps.RegisterFile (GF := GF)) $$ [$Hg] as Hg
  try wp_auto
  ihave Hown : EtcdGrove.ownInitLb get_is_pkg_init σ0 $$ [Hg]
  · iunfold EtcdGrove.ownInitLb; iexists σg; iframe Hg Hok; ipureintro; exact Hle
  ipersist HerrFrameTooLarge
  ipersist HerrFrameTooLong
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  iunfold _root_.Perennial.rabia.internal.message.msgFact
  iexists _, _
  iframe HerrFrameTooLarge HerrFrameTooLong
  ipureintro
  simp [interface.mkOk]

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
