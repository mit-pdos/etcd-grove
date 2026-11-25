/- Lean-first (no Rocq counterpart).

# A configuration change's bytes (`PutConfChange`, 2026-11-22)

`encCC o`: what `PutConfChange` (`examples/raft/kvraft/client.go`) appends for the change `o`: 1 then its
type and node id (8 bytes each) for a `ConfChange`; 2 then its transition, the number of its changes and
each change's type and node id for a `ConfChangeV2`. The enums are `int32`, widened to `uint64` with
their sign (`W64 (sint.Z t)`), as Go's conversion does. `encCC_length`: at most `17 + 16 n`, `n` its changes.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Codec
public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Pure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A `ConfChangeSingle`'s bytes. -/
def encCCS (c : ConfChangeSingleM) : List w8 :=
  u64Le (W64 (sint.Z c.Type')) ++ u64Le c.NodeId'

/-- The changes' bytes, in order. -/
def encCCSs : List ConfChangeSingleM → List w8
  | [] => []
  | c :: cs => encCCS c ++ encCCSs cs

/-- See the file header. -/
def encCC : ConfChangeIM → List w8
  | .v1 m => 1 :: (u64Le (W64 (sint.Z m.type)) ++ u64Le m.nodeId)
  | .v2 m => 2 :: (u64Le (W64 (sint.Z m.transition)) ++ u64Le (W64 m.changes.length) ++
      encCCSs m.changes)

theorem encCCSs_snoc (cs : List ConfChangeSingleM) (c : ConfChangeSingleM) :
    encCCSs (cs ++ [c]) = encCCSs cs ++ encCCS c := by
  induction cs with
  | nil => simp [encCCSs]
  | cons d ds ih => simp [encCCSs, ih, List.append_assoc]

theorem encCCSs_length (cs : List ConfChangeSingleM) : (encCCSs cs).length = 16 * cs.length := by
  induction cs with
  | nil => simp [encCCSs]
  | cons d ds ih => simp [encCCSs, encCCS, ih, u64Le_length]; omega

/-- At most `17 + 16 n` bytes, `n` the changes as `raft_kvreconf.ccToV2` sees them. -/
theorem encCC_length (o : ConfChangeIM) :
    (encCC o).length ≤ 17 + 16 * (raft_kvreconf.ccToV2 o).changes.length := by
  cases o with
  | v1 m =>
    simp [encCC, u64Le_length]
  | v2 m =>
    simp [encCC, u64Le_length, encCCSs_length, raft_kvreconf.ccToV2]; omega

end pure

end kvraft
end EtcdGrove
end Perennial
