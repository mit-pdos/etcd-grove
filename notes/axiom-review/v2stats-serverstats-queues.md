# `v2stats.ServerStats.{Recv,Send}AppendReq`: the rate queues' premise (rafthttpfix, 2026-11-20)

Found by prove-etcdserver (code reading, `notes/axiom-review/etcdserver-observers-v2stats.md`, ledger
2026-11-20 "`v2stats.ServerStats.RecvAppendReq`/`SendAppendReq` panic on a zero `ServerStats`"), which
recorded it and left the fix to the group owning the callers' invariants (rafthttp's). Fixed here.

## The defect

Both axioms (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/ServerStats__{Recv,Send}AppendReq.lean`)
took `st ≠ null` only. At the etcd pin (`server/etcdserver/api/v2stats/server.go:91-128`, `queue.go:62-63`)
each method locks the stats and calls `ss.recvRateQueue.Insert(...)` / `ss.sendRateQueue.Insert(...)`,
and `Insert` starts with `q.rwl.Lock()`, dereferencing `q`. Only `NewServerStats` (`server.go:33-45`)
allocates the queues; `ServerStats` is exported, so `(&v2stats.ServerStats{}).RecvAppendReq("a", 1)` (or
`SendAppendReq(1)`) panics with a nil pointer dereference, while the axioms proved that it returns. Not
reachable from etcd, which only passes `NewServerStats`' result (`NewServer`'s `sstats`, stored in the
server's `stats` and the transport's `ServerStats`). No Go counterexample was added: the panic is a plain
nil dereference of a field the zero value leaves nil.

`BecomeLeader`, `FollowerStats.Succ`/`Fail` touch no queue: their specs stay as they were.

## The fix

* `v2stats.isServerStats ss` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/Defs.lean`),
  persistent: `□` of an opaque `v2stats.serverStatsRaw ss`. Opaque because `ServerStats`' type has an
  anonymous struct field (`serverStats.LeaderInfo`), which Goose does not translate
  (`serverStats.underlying` is opaque), so the fields cannot be named. `opaque` adds no axiom; the only
  source of the fact is `NewServerStats`' axiom, and its only consumers are the two methods' axioms, so
  together they state: "the methods return on stats `NewServerStats` made" (the spec plan's
  `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/Api.lean` has the same
  `isServerStats`).
* `v2stats.NewServerStats.spec`'s post: `⌜p ≠ null⌝ ∗ v2stats.isServerStats p` (a strengthening).
* `RecvAppendReq.spec`, `SendAppendReq.spec`: the premise `v2stats.isServerStats st` added.
* Threaded: `srvProcOk` (`InvNet.lean`, the server's `stats` field) for `EtcdServer.Process`;
  `rafthttp.Transport.Start.spec`'s premise (`v2stats.isServerStats tv.ServerStats'`) and `trFixed`
  (`rafthttp/Transport.lean`) for `Transport.Send`; `NewServer`/`NewServerR` give both from
  `NewServerStats`' post.

The trust base's statements change (three axioms' texts), its count does not.
