/-
The trust boundary for `proto.Unmarshal` of empty bytes into a raft v3.7 `*pb.ConfChangeV2`
(2026-10-28, the unified node API's stage U5, `notes/raft-unified-plan.md`; approved by the user the
same day). `ccDecodeV2` (`Proof/go_etcd_io/raft/v3/CCModel.lean`) is opaque: nothing else says what
it gives for a particular byte string. Raft's leader proposes its own automatic leave of a joint
configuration as an `EntryConfChangeV2` with empty data (`raft.go:742-763`, `confChangeToMsg(nil)`;
`raftpb/confchange.go:40-45`) and decodes every conf entry it appends (`raft.go:1320`); an
application decodes the entry too when it applies it.
-/
module

public import Proof.go_etcd_io.raft.v3.CCModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- The empty `ConfChangeV2`: the automatic transition (`ConfChangeTransitionAuto`, `0`), no changes,
no context. -/
def ConfChangeV2M.empty [GooseExts] : ConfChangeV2M := ⟨W32 0, [], []⟩

/-- `proto.Unmarshal` decodes the empty encoding to the message with every field unset (protobuf's
wire format: a message is a sequence of fields, and the empty sequence sets none; protobuf-go
v1.36.11 `proto/decode.go`, `unmarshal` resets the message and its loop over the input runs zero
times). Unprovable here: `ccDecodeV2` is opaque. -/
axiom ccDecodeV2_nil [GooseExts] : ccDecodeV2 [] = some ConfChangeV2M.empty

end EtcdGrove
end Perennial
