/-
## `(*snapshotHandler).ServeHTTP(w, r)`

**Users.** `Transport.Handler`'s mux at `/raft/snapshot`.

**Proof sketch.** The method, the headers, `addRemoteFromRequest`; `messageDecoder.decodeLimit(64 MiB)` (a message `m'`; the body's prefix knowledge, `raftProto`'s `bodyPre` (round 1), says the bytes read so far are a prefix of the frame of an encoding of a `MsgSnap` `m` with `msgSent` and a deposit, followed by a stream of an image `img` with `snapImg ν i img`: frames self-delimiting, `m'` is `m`, so its snapshot and metadata are non-nil before the body ends, `msgSent_snap.spec`); a non-`MsgSnap`: 400 (none comes); `SaveDBFrom(r.Body, index)` with `readerAt_dbReader.spec` (the rest of the body: a stream of `img`) and the client's update from `saveOk ν sd` at `□ ν.img i img` (2e's spec: committed, `ν.dbIn i`; or an error, nothing saved, 500); the deposit opened with the ticket; `Process` with `recvd` (`dbIn`); `204`.

**Changes.** Restated: the snapshot directory invariant (`snapDirInv`, `snapSaved`) is the client's, over 2e's `snapDbs`, through `saveOk` (round 1: the file kept may be an earlier stream's; the client's invariant says what it holds).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) **Serves a snapshot POST**: the envelope's `MsgSnap` decoded, the rest of the body saved as the database of its index (the client's `saveOk` update, giving `dbIn`), then delivered to `Process` with `recvd`, answered `204`; or refused or failed. -/
def snapshotHandler.ServeHTTP.spec : Prop :=
  ∀ (hp : Loc) (ν : Net GF) (lid : w64) (w : GoInterface) (r : Loc) (R : Http.HReq) (τ : GName) (rd : GoInterface),
  ⊢ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ shAt hp ν lid ∗ Http.servePre (raftProto ν) go!"/raft/snapshot" w r R τ rd) -∗
    WP (App (App (Val (hp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotHandler.ty @!! go!"ServeHTTP")) (Val #w)) (Val #r))
    {{ v, Http.serveDone (raftProto ν) w R τ v }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
