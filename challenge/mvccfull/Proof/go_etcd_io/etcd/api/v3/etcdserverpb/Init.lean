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
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.sync.Link
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3
public import Code.go_etcd_io.raft.v3.confchange
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.raft.v3.tracker
public import Code.google_golang_org.protobuf.proto
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.bytes
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.encoding.binary
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.io
public import Perennial.Code.iter
public import Perennial.Code.log
public import Perennial.Code.math
public import Perennial.Code.slices
public import Perennial.Code.sort
public import Perennial.Code.strconv
public import Perennial.Code.strings
public import Perennial.Code.sync
public import Perennial.Code.sync.atomic
public import Perennial.Code.time
public import Perennial.Code.«unsafe»

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- **The trust boundary: `go_etcd_io.etcd.api.v3.etcdserverpb`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1», init.«2»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

namespace go_etcd_io.etcd.api.v3.etcdserverpb

end go_etcd_io.etcd.api.v3.etcdserverpb

end init

end Perennial
