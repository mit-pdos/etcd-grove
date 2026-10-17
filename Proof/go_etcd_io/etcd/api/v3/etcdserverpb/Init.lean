/-
Package initialization of `go_etcd_io.etcd.api.v3.etcdserverpb`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`etcdserverpbInit`, `cache/v3/Base.lean`): the sort enumerations' name maps. Its
initializer allocates and sets the translated gRPC service descriptors (`KV_ServiceDesc`, ...:
`grpc.ServiceDesc` literals), initializes its imports and runs its other variables' untranslated
initializers (the generated protobuf descriptors and enum maps): the trust-boundary axioms
`<X>_init` state the two the fact reads, `opaqueInitsOk` the others.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.membershippb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.protobuf.runtime.protoimpl.Init

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

section opaqueInits
namespace go_etcd_io.etcd.api.v3.etcdserverpb
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.api.v3.etcdserverpb`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([file_etcdserver_proto_msgTypes.init,
        file_etcdserver_proto_goTypes.init,
        file_etcdserver_proto_depIdxs.init,
        file_raft_internal_proto_msgTypes.init,
        file_raft_internal_proto_goTypes.init,
        file_raft_internal_proto_depIdxs.init,
        AlarmType_name.init,
        AlarmType_value.init,
        RangeRequest_SortOrder_value.init,
        RangeRequest_SortTarget_value.init,
        Compare_CompareResult_name.init,
        Compare_CompareResult_value.init,
        Compare_CompareTarget_name.init,
        Compare_CompareTarget_value.init,
        WatchCreateRequest_FilterType_name.init,
        WatchCreateRequest_FilterType_value.init,
        AlarmRequest_AlarmAction_name.init,
        AlarmRequest_AlarmAction_value.init,
        DowngradeRequest_DowngradeAction_name.init,
        DowngradeRequest_DowngradeAction_value.init,
        file_rpc_proto_enumTypes.init,
        file_rpc_proto_msgTypes.init,
        file_rpc_proto_goTypes.init,
        file_rpc_proto_depIdxs.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `RangeRequest_SortOrder_name = map[int32]string{...}` (`rpc.pb.go`): the enumeration's names, keys `0` to `2`. -/
axiom RangeRequest_SortOrder_name_init :
    {{ (True : IProp GF) }} (App (Val RangeRequest_SortOrder_name.init) (Val #()))
    {{ RET #(); ∃ (mp : Loc) (M : GMap w32 GoString), globalAddr RangeRequest_SortOrder_name ↦ mp ∗ mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 2⌝ }}

/-- `RangeRequest_SortTarget_name = map[int32]string{...}` (`rpc.pb.go`): the enumeration's names, keys `0` to `4`. -/
axiom RangeRequest_SortTarget_name_init :
    {{ (True : IProp GF) }} (App (Val RangeRequest_SortTarget_name.init) (Val #()))
    {{ RET #(); ∃ (mp : Loc) (M : GMap w32 GoString), globalAddr RangeRequest_SortTarget_name ↦ mp ∗ mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝ }}

end go_etcd_io.etcd.api.v3.etcdserverpb
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace go_etcd_io.etcd.api.v3.etcdserverpb

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Auth_ServiceDesc _ as HAuth_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Maintenance_ServiceDesc _ as HMaintenance_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Cluster_ServiceDesc _ as HCluster_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Lease_ServiceDesc _ as HLease_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Watch_ServiceDesc _ as HWatch_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) KV_ServiceDesc _ as HKV_ServiceDesc
  wp_apply _root_.Perennial.google_golang_org.grpc.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.api.v3.authpb.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.api.v3.membershippb.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.google_golang_org.protobuf.runtime.protoimpl.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk file_etcdserver_proto_msgTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_etcdserver_proto_goTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_etcdserver_proto_depIdxs.init (by mem_tac))
  wp_apply (opaqueInitsOk file_raft_internal_proto_msgTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_raft_internal_proto_goTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_raft_internal_proto_depIdxs.init (by mem_tac))
  wp_apply (opaqueInitsOk AlarmType_name.init (by mem_tac))
  wp_apply (opaqueInitsOk AlarmType_value.init (by mem_tac))
  wp_apply RangeRequest_SortOrder_name_init as ⟨%mpRangeRequest_SortOrder_name, %MRangeRequest_SortOrder_name, HRangeRequest_SortOrder_name, #SRangeRequest_SortOrder_name, %PRangeRequest_SortOrder_name⟩
  wp_apply (opaqueInitsOk RangeRequest_SortOrder_value.init (by mem_tac))
  wp_apply RangeRequest_SortTarget_name_init as ⟨%mpRangeRequest_SortTarget_name, %MRangeRequest_SortTarget_name, HRangeRequest_SortTarget_name, #SRangeRequest_SortTarget_name, %PRangeRequest_SortTarget_name⟩
  wp_apply (opaqueInitsOk RangeRequest_SortTarget_value.init (by mem_tac))
  wp_apply (opaqueInitsOk Compare_CompareResult_name.init (by mem_tac))
  wp_apply (opaqueInitsOk Compare_CompareResult_value.init (by mem_tac))
  wp_apply (opaqueInitsOk Compare_CompareTarget_name.init (by mem_tac))
  wp_apply (opaqueInitsOk Compare_CompareTarget_value.init (by mem_tac))
  wp_apply (opaqueInitsOk WatchCreateRequest_FilterType_name.init (by mem_tac))
  wp_apply (opaqueInitsOk WatchCreateRequest_FilterType_value.init (by mem_tac))
  wp_apply (opaqueInitsOk AlarmRequest_AlarmAction_name.init (by mem_tac))
  wp_apply (opaqueInitsOk AlarmRequest_AlarmAction_value.init (by mem_tac))
  wp_apply (opaqueInitsOk DowngradeRequest_DowngradeAction_name.init (by mem_tac))
  wp_apply (opaqueInitsOk DowngradeRequest_DowngradeAction_value.init (by mem_tac))
  wp_apply (opaqueInitsOk file_rpc_proto_enumTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_rpc_proto_msgTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_rpc_proto_goTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_rpc_proto_depIdxs.init (by mem_tac))
  -- translated initializer of KV_ServiceDesc))
  -- translated initializer of Watch_ServiceDesc))
  -- translated initializer of Lease_ServiceDesc))
  -- translated initializer of Cluster_ServiceDesc))
  -- translated initializer of Maintenance_ServiceDesc))
  -- translated initializer of Auth_ServiceDesc))
  repeat (wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %_ ⟨-, -⟩; wp_auto)
  ipersist HRangeRequest_SortOrder_name
  ipersist HRangeRequest_SortTarget_name
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold go_etcd_io.etcd.cache.v3.etcdserverpbInit
  iframe #
  ipureintro
  exact ⟨PRangeRequest_SortOrder_name, PRangeRequest_SortTarget_name⟩


end go_etcd_io.etcd.api.v3.etcdserverpb

end init

end Perennial
