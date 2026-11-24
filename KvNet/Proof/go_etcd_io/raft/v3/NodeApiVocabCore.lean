-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/NodeApiVocabCore.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The declarations `StorContents`, `StorContents.b`, `StorContents.last`, `StorContents.commit` of
`Proof/go_etcd_io/raft/v3/NodeApiVocab.lean`, split from it so that the WAL
(`Proof/go_etcd_io/etcd/server/v3/storage/wal/`) imports them without the rest (until 2026-11-15 an
extract of `etc/gen-part-copies.py` for the part `LinuxFs/`; notes/wal-lean-integration.md). The
source imports this module.
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.PbModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section extract
variable [GooseExts]

/-- A storage's contents (durability, candidate 12 §2): hard state, snapshot, log base, entries
above it. -/
structure StorContents where
  hs : HardStateM
  snap : Option SnapshotM
  base : entryID
  ents : List EntryM

/-- The base's index. -/
def StorContents.b (σ : StorContents) : Nat := uint.nat σ.base.index'

/-- The last index. -/
def StorContents.last (σ : StorContents) : Nat := σ.b + σ.ents.length

/-- The stored commit index. -/
def StorContents.commit (σ : StorContents) : Nat := uint.nat σ.hs.Commit'

end extract

end EtcdGrove
end Perennial
