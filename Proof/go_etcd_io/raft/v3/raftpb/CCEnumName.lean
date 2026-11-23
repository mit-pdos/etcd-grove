/-
**The names of raft's conf-change types and transitions** (#25, 2026-11-23): what
`ConfChangeType.String` and `ConfChangeTransition.String` return (`raftpb.ccTypeString`,
`raftpb.ccTransitionString`, the results of `Spec/go_etcd_io/raft/v3/raftpb/ConfChangeType__String.lean`
and `ConfChangeTransition__String.lean`), as `MsgTypeName.lean`'s `raftpb.msgTypeString` for
`MessageType`.
-/
module

public import Proof.go_etcd_io.raft.v3.Base
public import Proof.strconv.FormatIntDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- What `t.String()` of a `ConfChangeType` returns: `ConfChangeType_name`'s entry at `t`, else `t`
in decimal (`strconv.Itoa(int(t))`, protobuf-go's `EnumStringOf`'s fallback). -/
def raftpb.ccTypeString (t : w32) : GoString :=
  match go_etcd_io.raft.v3.raftpb.ccTypeNames !! t with
  | some s => s
  | none => fmtInt (W64 (sint.Z t)) (W64 10)

/-- What `t.String()` of a `ConfChangeTransition` returns: `ConfChangeTransition_name`'s entry at
`t`, else `t` in decimal. -/
def raftpb.ccTransitionString (t : w32) : GoString :=
  match go_etcd_io.raft.v3.raftpb.ccTransitionNames !! t with
  | some s => s
  | none => fmtInt (W64 (sint.Z t)) (W64 10)

end EtcdGrove
end Perennial
