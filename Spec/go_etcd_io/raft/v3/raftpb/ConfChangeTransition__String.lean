/-
`raftpb.ConfChangeTransition.String` (`raftpb/raft.pb.go`, protoc-gen-go): the name of a value, `ConfChangeTransition_name`'s entry,
else the decimal (protobuf-go's `EnumStringOf`). Trusted code since 2026-11-23 (#25, as
`MessageType.String`'s: `TrustedCode/go_etcd_io/raft/v3/raftpb.lean`, which argues the model is Go's;
trusted model approved by the coordinator under the user's delegation, review requested on #25);
names-only until then. `DescribeConfChange` formats it with `%v`.
-/
module

public import Proof.go_etcd_io.raft.v3.raftpb.CCEnumName

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

/-- `t.String()` returns `raftpb.ccTransitionString t`: `ConfChangeTransition_name`'s entry at `t`, else `t` in decimal. -/
abbrev raftpb.ConfChangeTransition.String.spec : Prop :=
  ∀ (t : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (t @!! raftpb.ConfChangeTransition.ty @!! go!"String")) (Val #()))
  {{ RET #(raftpb.ccTransitionString t); True }}

end spec

end EtcdGrove
end Perennial
