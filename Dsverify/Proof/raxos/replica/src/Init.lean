/-
Package initialization of `raxos.replica.src`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`srcState`, `Base.lean`): `Consensus_ServiceDesc` holds, read-only for good,
the descriptor of service `Consensus` (its three methods with their generated handlers, no
streams, its `HandlerType` the typed nil `(*ConsensusServer)(nil)`). Its initializer allocates
and sets the translated gRPC service descriptor (a `grpc.ServiceDesc` literal), initializes its
imports and runs the trusted initializers of protoc-gen-go's descriptor tables and `init` (models
in `TrustedCode/` that do nothing).
-/
module

public import Dsverify.Proof.raxos.replica.src.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.fmt.Link
public import Dsverify.Proof.github_com.go_redis.redis.v8.Init
public import Dsverify.Proof.google_golang_org.grpc.Init
public import Dsverify.Proof.google_golang_org.grpc.codes.Init
public import Perennial.Proof.io.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.math.rand.Link
public import Perennial.Proof.reflect.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.bufio.Init
public import Dsverify.Proof.google_golang_org.grpc.status.Init
public import Proof.google_golang_org.protobuf.reflect.protoreflect.Init
public import Proof.google_golang_org.protobuf.runtime.protoimpl.Init
public import Proof.net.Init
public import Proof.os.Init
public import Dsverify.Proof.raxos.common.Init
public import Dsverify.Proof.raxos.configuration.Init
public import Dsverify.Proof.raxos.proto.Init
public import Dsverify.Proof.raxos.proto.client.Init
public import Proof.runtime.PkgInitExt
public import Dsverify.Proof.runtime.PkgInitDsv
public import Dsverify.Proof.gopkg_in.yaml_v2.Init
public import Dsverify.Proof.encoding.gob.Init

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
variable [_root_.Perennial.google_golang_org.grpc.InitHyp GF]
variable [_root_.Perennial.github_com.go_redis.redis.v8.InitHyp GF]
variable [package_sem : _root_.Perennial.raxos.replica.src.Assumptions]

namespace raxos.replica.src

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.raxos.replica.src get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Consensus_ServiceDesc _ as HConsensus_ServiceDesc
  wp_call  -- File_replica_src_consensus_proto: its trusted initializer does nothing
  wp_call  -- file_replica_src_consensus_proto_rawDescOnce: its trusted initializer does nothing
  wp_apply (_root_.Perennial.raxos.proto.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd25⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd24⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (_root_.Perennial.raxos.configuration.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (_root_.Perennial.raxos.common.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (_root_.Perennial.net.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.bufio.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math.rand _root_.Perennial.math.rand.initialize'
      EtcdGrove.ExternalInit.math_rand _root_.Perennial.math.rand.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.github_com.go_redis.redis.v8 _root_.Perennial.github_com.go_redis.redis.v8.initialize'
      EtcdGrove.ExternalInit.github_com_go_redis_redis_v8 _root_.Perennial.github_com.go_redis.redis.v8.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (_root_.Perennial.google_golang_org.grpc.status.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.grpc.codes _root_.Perennial.google_golang_org.grpc.codes.initialize'
      EtcdGrove.ExternalInit.google_golang_org_grpc_codes _root_.Perennial.google_golang_org.grpc.codes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.grpc _root_.Perennial.google_golang_org.grpc.initialize'
      EtcdGrove.ExternalInit.google_golang_org_grpc _root_.Perennial.google_golang_org.grpc.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.reflect _root_.Perennial.reflect.initialize'
      EtcdGrove.ExternalInit.reflect _root_.Perennial.reflect.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.google_golang_org.protobuf.runtime.protoimpl.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.google_golang_org.protobuf.reflect.protoreflect.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.raxos.proto.client.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.os.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.log _root_.Perennial.log.initialize'
      EtcdGrove.ExternalInit.log _root_.Perennial.log.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_call  -- file_replica_src_consensus_proto_rawDesc: its trusted initializer does nothing
  wp_call  -- file_replica_src_consensus_proto_rawDescData: its trusted initializer does nothing
  wp_call  -- file_replica_src_consensus_proto_msgTypes: its trusted initializer does nothing
  wp_call  -- file_replica_src_consensus_proto_goTypes: its trusted initializer does nothing
  wp_call  -- file_replica_src_consensus_proto_depIdxs: its trusted initializer does nothing
  -- translated initializer of Consensus_ServiceDesc))
  try wp_auto
  wp_apply (wp_slice_literal (V := google_golang_org.grpc.MethodDesc) (t := google_golang_org.grpc.MethodDesc.ty) [⟨go!"ESP", functions _Consensus_ESP_Handler []⟩, ⟨go!"FetchBatches", functions _Consensus_FetchBatches_Handler []⟩, ⟨go!"InformDecision", functions _Consensus_InformDecision_Handler []⟩])
  isplitr
  · ipureintro; rfl
  iintro %ml ⟨Hml, -⟩
  try wp_auto
  wp_apply (wp_slice_literal (V := google_golang_org.grpc.StreamDesc) (t := google_golang_org.grpc.StreamDesc.ty) [])
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨-, -⟩
  try wp_auto
  ipersist HConsensus_ServiceDesc
  ipersist Hml
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  unfold srcState
  imodintro
  iexists _
  iframe HConsensus_ServiceDesc
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  iexact Hml

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.raxos.replica.src get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end raxos.replica.src

end init

end Perennial
