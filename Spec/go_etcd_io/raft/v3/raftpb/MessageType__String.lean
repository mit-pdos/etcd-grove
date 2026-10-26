/-
`raftpb.MessageType.String` (`raftpb/raft.pb.go`, protoc-gen-go; names-only in the translation,
`Code/go_etcd_io/raft/v3/raftpb.toml`): the trust boundary, as `ConfChangeType.String`'s. Its
`String()` returns some string (protoimpl's enum name or the number); rafthttp's stream reader logs
a dropped message's type (2026-10-23, rafthttp stage 5c).
-/
module

public import Spec.fmt.Errorf
public import Code.go_etcd_io.raft.v3.raftpb

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

/-- `t.String()` of a message type returns some string. -/
abbrev raftpb.MessageType.String.spec : Prop :=
  ∀ (t : w32),
    ⊢ fmt.stringMethodSpec (GF := GF) (interface.mk raftpb.MessageType.ty #t) go!"String"

end spec

end EtcdGrove
end Perennial
