# Requirements on `go.etcd.io/etcd/server/v3/etcdserver/api/v2stats` (batch 2e)

## from 2f

Provisional in `Rafthttp`'s `Api.lean`: `serverStatsOk s` (persistent: `SendAppendReq` locks
inside), `leaderStatsOwn s` (exclusive to the transport: `Follower(id)` adds under the stats' lock,
and `removePeer` deletes from `Followers` without it, under the transport's own lock;
`nonissues/etcd-rafthttp-leaderstats-followers-race.md`), `followerStatsOk fs` (persistent:
`Succ`, `Fail` lock inside). The specs: `NewServerStats`, `NewLeaderStats` give them;
`LeaderStats.Follower(id)` gives a `followerStatsOk`; `SendAppendReq`, `Succ`, `Fail` return.
```go
fs := t.LeaderStats.Follower(id.String())        // transport.go:309
t.ServerStats.SendAppendReq(proto.Size(m))       // transport.go:189
```
Used by: `Transport.Start.spec` (`trCfg`), `AddPeer`, `Send`, the msgappv2 encoder, the pipeline.
