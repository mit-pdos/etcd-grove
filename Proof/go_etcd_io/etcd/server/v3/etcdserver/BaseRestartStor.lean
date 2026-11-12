/-
**The raft storage a restart rebuilds** (restart S3, 2026-11-11; D2 (b)). Lean-first (no Rocq
counterpart).

`bootstrappedWAL.MemoryStorage` (`bootstrap.go:741-753`) rebuilds the raft storage from the WAL's
records: `NewMemoryStorage`, then `ApplySnapshot` of the snapshot `bootstrap` built (the WAL's newest
valid snapshot record's index and term, the backend's conf state: `bootstrap.go:107-115, 449-475`),
`SetHardState` of the read hard state, `Append` of the read entries. `memStorRestarted` is what that
leaves by raft's proved storage specs; it is the post of `bootstrappedWAL.MemoryStorage.spec`
(proved), and the restart contract's `bootOkR` states the restarted storage in its terms. (Until
2026-11-11 an opaque of `InvRestart.lean`.)
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Proof.go_etcd_io.raft.v3.NodeApiVocab

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The snapshot `bootstrap` applies to the restarted storage**: the WAL's base `σ.base` (the index
and term of its newest valid snapshot record, `(0, 0)` without one), no data, the conf state `cs`,
the backend's (`bootstrap.go:107-115`: `sn.Metadata.ConfState = &cs`). -/
def walSnapCS (σ : StorContents) (cs : ConfStateM) : SnapshotM :=
  SnapshotM.mk [] (SnapshotMetadataM.mk cs σ.base.index' σ.base.term')

theorem walSnapCS_index (σ : StorContents) (cs : ConfStateM) :
    uint.nat (walSnapCS σ cs).Metadata'.Index' = σ.b := rfl

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The `MemoryStorage` `bootstrappedWAL.MemoryStorage` rebuilds** from the WAL's records `σ` and
the backend's conf state `cs`, detached (no raft ghost yet): the storage's detached token at the
base and `walSnapCS σ cs` (`memStorFresh`), the hard state `σ.hs`, the compaction point and the
dummy entry at the base, the stored snapshot's lower bound there, the entries `σ.ents` owned above
the base, the end after them. -/
def memStorRestarted (ms : Loc) (γs : MemStorNames) (σ : StorContents) (cs : ConfStateM) :
    IProp GF :=
  iprop(memStorFresh ms γs σ.b (walSnapCS σ cs) ∗ memStorMeta ms γs σ.hs ∗
    memCompacted γs σ.b ∗ memLog γs σ.b DFrac.discard [memDummy (walSnapCS σ cs)] ∗
    memSnapLb γs σ.b ∗
    memLog γs (σ.b + 1) (DFrac.own 1) σ.ents ∗ memEnd γs (σ.last + 1))

end defs

end EtcdGrove
end Perennial
