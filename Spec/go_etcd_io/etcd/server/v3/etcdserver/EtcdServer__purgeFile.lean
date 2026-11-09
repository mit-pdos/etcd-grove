/-
## `(*EtcdServer).purgeFile()` (`server.go:608-625`)

**Users.** `Start` (attached goroutine).

**Proof sketch.** With `MaxWALFiles > 0`, `fileutil.PurgeFileWithDoneNotify` (trusted: it deletes
only files it can lock, i.e. released ones: `Wal.Recs.release`'s floor) runs with the
`Wal.walPurgeRight` taken out of `srvPurge`'s invariant; at `stopping` it waits for `wdonec` and puts
the right back (so the WAL's `Close` in the raft node's stop finds it, `walPurgeRight` of
`Wal/Api.lean`). A purge error is `Fatal` (no return).

**Changes** (from `specs-ref`'s `EtcdServer__purgeFile.lean`, which took no premise on `s`: the
sweep's logger-family survey): over `isServer` and the purge's handle; the snapshot dbs are not
purged here (the fork's change: `ReleaseSnapDBs` does it).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Purges released WAL files** until the server stops. -/
def EtcdServer.purgeFile.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvPurge s }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"purgeFile")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
