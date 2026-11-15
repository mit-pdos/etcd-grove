/-
## `(*snapshotHandler).ServeHTTP(w, r)`

**Users.** `Transport.Handler`'s mux at `/raft/snapshot`.

**Proof sketch.** The method, the headers, `addRemoteFromRequest`; `messageDecoder.decodeLimit(64 MiB)` (a message `m'`, `msgRecv`, with an encoding `e` whose `msgFrame` was read; the body's prefix knowledge, `raftProto`'s `bodyPre` (round 1), says the bytes read so far are a prefix of the frame of an encoding of a `MsgSnap` `m` with `msgSent` and a deposit, followed by a stream of an image `img` with `snapImg ν i img`: `msgFrame` self-delimiting and decoding a function (raftpb's `wire_fun`), `m'` is `m`, so its snapshot and metadata are non-nil before the body ends, `msgSent_snap.spec`); a non-`MsgSnap`: 400 (none comes; its log line's `m.GetType().String()` for a log line is raftpb's `MessageType.String` (a trust-boundary spec, requested of raft-conf-pb: verify-round A5 F1)); `SaveDBFrom(r.Body, index)` with `readerAt_dbReader.spec` (the rest of the body: a stream of `img`) and the client's two updates from `saveOk ν sd` at `□ ν.img i img` (exactly `SaveDBFrom`'s nested pair with `Q := ν.dbIn i`, at the entry `p` `saveOk` names, `Snap.inDir sd p`: the second update takes the client's `Backend.beRevs p os` at the directory fsync and gives `beNoRevert p`; 2e's spec: committed, `ν.dbIn i`; or an error, the first update given back, 500); the deposit opened with the ticket; `Process` with `recvd` (`dbIn`); `204`. `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** Restated: the snapshot directory invariant (`snapDirInv`, `snapSaved`) is the client's, over 2e's `snapDbs`, through `saveOk` (round 1: the file kept may be an earlier stream's; the client's invariant says what it holds). verify-round (A5 F4, A8 F8): `Process` gets `msgRecv`; second pass: `saveOk` supplies `SaveDBFrom`'s two updates (`snapSaving` between); the frame is the transparent `msgFrame` of raftpb's `msgEncodes`. verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`. Final relay round: `SaveDBFrom`'s second update takes the client's revert state of an entry (`Backend.beRev`) at the directory fsync, which `saveOk`'s second update supplies; statement unchanged. Verify round, crash pass: `saveOk`'s revert state is the list form `Backend.beRevs p os` (R-A8 N3); statement unchanged. Second crash pass (F-server-boot F4): `shAt hp ν lid` holds `saveOk ν lid sd`, whose commit gives `ν.dbIn lid i`, and `Process` gets `recvd ν lid m` (the receiver's own record, whatever `m.To` says: `Process` refuses another member's with a `403`); statement unchanged.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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
