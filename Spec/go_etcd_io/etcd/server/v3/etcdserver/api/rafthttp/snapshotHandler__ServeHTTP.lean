/-
## `(*snapshotHandler).ServeHTTP(w, r)`

**Users.** `Transport.Handler`'s mux at `/raft/snapshot`.

**Proof sketch.** The method, the headers, `addRemoteFromRequest`; `messageDecoder.decodeLimit(64 MiB)` (a message `m'`); a non-`MsgSnap`: 400; `SaveDBFrom(r.Body, index)` (2e: reads to `EOF`, saves the file, `dbSaved ss i bs`); at `EOF` the body knowledge: a frame of an encoding of a `MsgSnap` `m` with `msgSent` and a deposit, then an image with `snapImg` (frames self-delimiting: `m'` is `m`, its snapshot's index `i`); the deposit opened with the ticket; `Process` (`recvd` with `dbSaved`); `204`. The snapshot is non-nil (`msgSent_snap.spec`).

**Changes.** Restated: the snapshot directory invariant (`snapDirInv`, `snapSaved`) is snap's `dbSaved` (2e).

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

/-- (internal) **Serves a snapshot POST**: the envelope's `MsgSnap` decoded, the rest of the body saved as the database of its index (`dbSaved`, a `snapImg` image), then delivered to `Process` with `recvd`, answered `204`; or refused or failed. -/
def snapshotHandler.ServeHTTP.spec : Prop :=
  ∀ (hp : Loc) (ν : Net) (lid : w64) (w : GoInterface) (r : Loc) (R : Http.HReq) (τ : GName) (rd : GoInterface),
  ⊢ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ shAt hp ν lid ∗ Http.servePre (raftProto ν) go!"/raft/snapshot" w r R τ rd) -∗
    WP (App (App (Val (hp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotHandler.ty @!! go!"ServeHTTP")) (Val #w)) (Val #r))
    {{ v, Http.serveDone (raftProto ν) w R τ v }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
