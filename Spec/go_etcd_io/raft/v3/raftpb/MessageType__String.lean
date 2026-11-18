/-
`raftpb.MessageType.String` (`raftpb/raft.pb.go`, protoc-gen-go): the name of a message type,
`MessageType_name`'s entry, else the decimal (protobuf-go's `EnumStringOf`). Trusted code since
2026-11-09 (Q9 of `notes/trace-validation-plan.md`: `TrustedCode/go_etcd_io/raft/v3/raftpb.lean`,
which argues the model is Go's); until then names-only, with a trust-boundary axiom that it returns
some string (rafthttp stage 5c, 2026-10-23), which `fmt.stringMethodSpec_of_wp` derives from this
one (`Proof/go_etcd_io/raft/v3/raftpb/MsgTypeName.lean`, with the result `raftpb.msgTypeString`).
-/
module

public import Proof.go_etcd_io.raft.v3.raftpb.MsgTypeName

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `t.String()` returns `raftpb.msgTypeString t`: `MessageType_name`'s entry at `t`, else `t` in
decimal. -/
abbrev raftpb.MessageType.String.spec : Prop :=
  ∀ (t : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (t @!! raftpb.MessageType.ty @!! go!"String")) (Val #()))
  {{ RET #(raftpb.msgTypeString t); True }}

end spec

end EtcdGrove
end Perennial
