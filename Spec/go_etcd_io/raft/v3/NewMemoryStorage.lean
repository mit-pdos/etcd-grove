/-
## `NewMemoryStorage()`

**Users.** etcd's `bootstrappedWAL.MemoryStorage` (`bootstrap.go:741`: detached, rebuilt from the WAL),
`raftNode.start` (`raft.go:287`, `292`: the batch's snapshot and entries), `EtcdServer.snapshot`
(`server.go:2132`: `CreateSnapshot` at the applied index), `EtcdServer.compact`/`purge`
(`server.go:2180`: `Compact`), `EtcdServer.getSnapshot` (`server.go:755`); the examples' storages
(`kvdurable/storage.go`, a wrapper calling these under its own lock). Snippet: `storage.go`. **Proof sketch.** The dummy entry, `EnsureSnapshot`
(raftpb); the lock invariant allocated with the contents' ghost authority. **Changes.** The contents
are a `StorState` (was `memStorFresh`'s compaction point and snapshot, with `MemStorNames`).
-/
module

public import Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- An empty `MemoryStorage`. -/
def NewMemoryStorage.spec : Prop :=

  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val (@! go_etcd_io.raft.v3.NewMemoryStorage)) (Val #()))
  {{ (ms : Loc), RET #ms; memStor ms StorState.empty }}

end spec
end Raft
end EtcdGrove
end Perennial
