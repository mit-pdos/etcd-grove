/-
`proto.Equal` (gogoproto, `github.com/gogo/protobuf/proto/equal.go`; names-only): the trust
boundary, for the one call raft makes, `ConfChangeV2.LeaveJoint`'s. Lean-first (no Rocq
counterpart); see `InvConfChangeMsg.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Trust boundary.** gogoproto's `Equal(a, b)` is Go reflection (`reflect.ValueOf`,
`GetProperties`), which Goose does not model, so this is an `axiom`. Stated for
`LeaveJoint`'s call only: `a = &c` with `c.Context` set to `nil`, `b = &ConfChangeV2{}`.

Read against `equal.go` (gogo/protobuf v1.3.2, raft's `go.mod`): both arguments are non-nil
pointers of the same type, so `equalStruct` compares the structs field by field (with
`GetProperties`), and `ConfChangeV2` has exactly the three fields `Transition`, `Changes`,
`Context` (`raft.pb.go`; no `XXX_` fields, no extensions). `Transition` is a non-nullable
`int32` enum: `==`, so equal iff `Transition = 0`. `Changes` is a repeated field (a slice of
non-bytes): equal only if the lengths are, and the zero value's is `0`; at length `0` there are
no elements to compare. `Context` is a proto2 `bytes` field, `nil` on both sides: equal. So the
result is `Transition = 0 ∧ len(Changes) = 0`. Only the two structs are read (no element of
`Changes`: the lengths differ or are `0`). -/
abbrev gogoproto.Equal.spec : Prop :=
  ∀ (p q : Loc) (v : raftpb.ConfChangeV2) (dq dq' : DFrac),
  v.Context' = slice.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.gogo.protobuf.proto ∗
      p ↦{dq} v ∗ q ↦{dq'} (zero_val raftpb.ConfChangeV2) }}
    (App (App (Val #(functions github_com.gogo.protobuf.proto.Equal []))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #p)))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #q)))
  {{ RET #(decide (v.Transition' = W32 0 ∧ v.Changes'.len = W64 0));
      p ↦{dq} v ∗ q ↦{dq'} (zero_val raftpb.ConfChangeV2) }}

end spec

end EtcdGrove
end Perennial
