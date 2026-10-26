---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#21880 pr open: grpc-proxy honors the client's WatchId (#12819); related, not a fix: with it the bug would also reach clients behind the proxy
  - etcd-io/etcd#21065 pr open: in-process watch deadlock when recvLoop blocks (#18879, #20716); related, not a fix: why the candidate's creates wait only on streams with client-chosen ids
candidate: issues/upstream/etcd-watch-id-reuse-stale-events/
---

# A reused watch id can deliver the canceled watcher's events on the new watch

- **Status**: bug, reproduced (2026-10-16 at upstream `main` b25719d10; again 2026-10-18 at
  22cc5d9ac; again 2026-10-21 at bf9cadf04) by the integration test `TestV3WatchReuseCanceledID` on
  the fork branch `fix/etcd-watch-id-reuse-stale-events` (the upstream candidate): one raw watch
  stream, watch id 1 on `a`, twenty 50 KiB puts of `a` while the client does not read (gRPC flow
  control holds them in mvcc's channel), cancel (the test waits for the member's watcher count to
  drop), re-create id 1 on `b` from the next revision, put `b`: the new watch receives 9-15 events of
  `a` before `b` (failed 80 of 80 runs at bf9cadf04). The auto-assigned-id variant below is
  reproduced too (2026-10-21, a scratch copy of the test: 10 of 10 failed).
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

  `sendLoop` buffers a response whose id is not announced under that id, and flushes the
  buffer when the id's created response goes out. The cancel case removes the id from `ids` but
  leaves `pending[id]`:

  ```go
  // server/etcdserver/api/v3rpc/watch.go:470-476 and 534-552 (etcd main f061acd09)
  			if wresp.WatchID != clientv3.InvalidWatchID {
  				if _, okID := ids[wresp.WatchID]; !okID {
  					// buffer if id not yet announced
  					wrs := append(pending[wresp.WatchID], wr) // <-
  					pending[wresp.WatchID] = wrs
  					continue
  				}
  	// ...
  			if c.Canceled && wid != clientv3.InvalidWatchID {
  				delete(ids, wid) // <- pending[wid] is kept
  				continue
  			}
  			if c.Created {
  				// flush buffered events
  				ids[wid] = struct{}{}
  				for _, v := range pending[wid] { // <-
  					mvcc.ReportEventReceived(len(v.Events))
  					if err := sws.gRPCStream.Send(v); err != nil {
  	// ...
  					}
  				}
  ```

  **Variant** (2026-10-15, unit W-M; reproduced 2026-10-21): the same reuse happens without a
  second explicit id (explicit 1 canceled, then two creates without an id get 0 and 1). mvcc's
  `watchStream.Watch` with `AutoWatchID` skips only the ids live on the stream (`for
  ws.watchers[ws.nextID] != nil { ws.nextID++ }`), so an explicit id `X` at or above `nextID`
  that was canceled can later be assigned automatically to a new watch, whose created response
  then flushes the canceled watcher's buffered responses as above. A stream on which every
  create uses `AutoWatchID` (etcd's client: `toPB` sets no `WatchId`) never reuses an id: mvcc's
  `idAssigned_agree` (an assigned id names one watcher for good; `notes/status-history.md`, "W-M").

  ```go
  // server/storage/mvcc/watcher.go:128-136 (etcd main f061acd09)
  	if id == clientv3.AutoWatchID {
  		for ws.watchers[ws.nextID] != nil { // <- skips only live ids
  			ws.nextID++
  		}
  		id = ws.nextID
  		ws.nextID++
  	} else if _, ok := ws.watchers[id]; ok { // <- a canceled id is accepted again
  		return -1, ErrWatcherDuplicateID
  	}
  ```
- **Expected**: the documentation says nothing of id reuse; a client re-creating a watch with
  the same id expects only the new watch's events after its created response.
- **How the proof handles it**: nothing is assumed: `sendLoop`'s proof attributes each mvcc
  response to its watcher, not to its id (`WatchRespM.src`, `mvccOk` over `r.w`;
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/WatchSendModel.lean`'s `send_claim`
  orders each watcher's responses, whatever ids they share). A client of `watchStreamSpec` must
  not identify a watch by its id across a cancel (the client hop, `notes/status-history.md`, "The watch
  slice").
- **Possible fixes**: dropping `pending[X]` on a cancel (`delete(pending, X)` with the
  `delete(ids, X)`) is not enough: tried on the reproduction, it still fails 10 of 10, since most of
  the old watcher's responses are taken from mvcc's channel after the new created response, when `X`
  is announced again, and are sent directly. The upstream candidate drops a canceled watcher's
  responses taken after its canceled response, and, on a stream where some create has set
  `WatchId`, makes each create in `recvLoop` wait until `sendLoop` has taken the responses queued
  when the last earlier cancel was taken (at most the channel's 128); a stream with only automatic
  ids never reuses one, and a wait there would risk the in-process deadlock of etcd-io/etcd#20716
  (`issues/upstream/etcd-watch-id-reuse-stale-events/meta.md` has the costs and the alternatives:
  tagging mvcc's responses with the watcher, rejecting a create of a canceled id). Documentation instead
  (2026-10-23, the user's review: a stream uses either automatic or explicit ids, and never reuses a
  canceled one): decided against as the fix, since the server breaks what `rpc.proto` already promises
  and today's text allows the reuse; asked in the issue as questions, with the documentation-only
  shape ready if the maintainers prefer it (the candidate's `meta.md`, "If a reviewer asks"). Also noticed:
  [etcd-watch-canceled-pending-retained](nonissues/etcd-watch-canceled-pending-retained.md).
- **Found**: 2026-10-14, the watch slice's unit W-S (`sendLoop`'s proof: the per-id model of the
  buffering, `SendInv`).
