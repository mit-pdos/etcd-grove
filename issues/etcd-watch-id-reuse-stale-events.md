# A reused watch id can deliver the canceled watcher's events on the new watch

- **Status**: open (not reported; not reproduced: the analysis below, from the proof).
- **Where**: `server/etcdserver/api/v3rpc/watch.go` at the pinned revision (`upamanyus/etcd`
  `bc8b52a50`): `serverWatchStream.sendLoop`, the buffering of a response whose id is not
  announced (lines 470–476: `pending[wresp.WatchID] = append(...)`), the cancel case
  (534–537: `delete(ids, wid)`, the id's buffered responses kept), the created case (538–552:
  `pending[wid]` flushed to the client); `recvLoop`'s create with a client-chosen `WatchId`
  (`WatchCreateRequest.watch_id`, documented: "If watch_id is provided and non-zero, it will be
  assigned to this watcher").
- **What happens**: the mvcc watch stream's channel is shared by all watchers of a gRPC stream,
  and `sendLoop` takes responses from it and from the control stream in either order (`select`).
  A client that cancels its watch `X` and creates a new watch with the same explicit id `X`:
  1. `recvLoop` cancels the mvcc watcher and queues the canceled response; responses of the old
     watcher already in the mvcc channel stay there;
  2. `sendLoop` may take the canceled response first: `delete(ids, X)`; it then takes the old
     watcher's responses: `X` is not announced, so they are buffered in `pending[X]`;
  3. the new create with id `X` succeeds in mvcc (the old watcher is gone) and its created
     response is sent; `sendLoop` flushes `pending[X]`: the old watcher's events reach the client
     on the new watch `X`, after its created response, with revisions that may be below the new
     watch's start revision and outside its range.

  The client cannot tell them apart (the response carries only the id).
- **Expected**: the documentation says nothing of id reuse; a client re-creating a watch with
  the same id expects only the new watch's events after its created response.
- **How the proof handles it**: nothing is assumed: `sendLoop`'s proof attributes each mvcc
  response to its watcher, not to its id (`WatchRespM.src`, `mvccOk` over `r.w`;
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/WatchSendModel.lean`'s `send_claim`
  orders each watcher's responses, whatever ids they share). A client of `watchStreamSpec` must
  not identify a watch by its id across a cancel (the client hop, `notes/STATUS.md`, "The watch
  slice").
- **Possible fixes**: on a cancel, drop `pending[X]` (`delete(pending, X)` with the
  `delete(ids, X)`, reporting the dropped events), or reject a create whose explicit id was
  canceled while its responses may still be in flight.
- **Found**: 2026-10-14, the watch slice's unit W-S (`sendLoop`'s proof: the per-id model of the
  buffering, `SendInv`).
