# Batches and waves

A batch is a set of interacting functions (an API and the code behind it), specified by one author
agent and judged by reviewers separate from it and from other batches (README.md, "The review of a
batch"). Waves go top-down: a wave's batches are the callers of the next wave's, and write their
needs of their callees into `req/`. Raft's chain starts with the client anchor: its top API (the
node) has its users' code already, and nothing in the KV chain is its callee.

Paths: `S = .lake/src` (links to the pinned Go sources: `server`, `client`, `api`, `pkg`, `cache`,
`raft`, `bbolt`); old specs in `specs-ref/Spec/<pkg>/` (the worktree
`/home/ubuntu/etcd-grove/.claude/worktrees/specs-ref`). "Functions": every function of the listed
Go files that has an old spec file, and any other function of those files that the batch's callers
or proof sketches need (say which you added); a function without an old spec that nothing needs
may be left out, listed as such.

| id | wave | batch | Go files | old specs (count) | status |
|---|---|---|---|---|---|
| W0 | 0 | **anchor**: the client-observable model (`api/v3/Model.lean`), the client vocabulary (`client/v3/Api.lean`: KV, and the slots watch/lease/auth/cluster will fill), the client's KV path, the ambient logger | `S/client/{kv,txn,op,compare,compact_op,sort,utils,ctx,retry}.go` (KV parts), `zap` boundary | client/v3 Op*, With*, kv, txn, Cmp, Compare, CompactOp, retryKVClient, ... (~120) | |
| R1 | 0 | raft node API: `node`, `RawNode`, `MemoryStorage`, `Storage`, `Ready`, `Config`, `StartNode`/`RestartNode` | `S/raft/{node,rawnode,storage,bootstrap,status,util}.go` | raft/v3 node, RawNode, MemoryStorage, Api, ... (~70) | |
| 1b | 1 | client watch | `S/client/watch.go` | watcher, watchGRPCStream, watcherStream, WatchResponse, OpWatch... (~40) | |
| 1c | 1 | client lease, lifecycle, auth, cluster, maintenance, interceptors | `S/client/{lease,client,auth,cluster,maintenance,retry_interceptor,block_logger,config,options,logger}.go`, `client/v3/{credentials,internal/*}`, `client/pkg/v3/*`, `client/v3/kubernetes` | lessor, Client, authClient, retry*Client, ... (~90) | |
| 1d | 1 | concurrency (Session, Mutex, Election, STM) | `S/client/concurrency/*.go` | 62 | |
| 1e | 1 | leasing KV | `S/client/leasing/*.go` | 66 | |
| 1f | 1 | recipes | `S/client/experimental/recipes/*.go` | 38 | |
| 1g | 1 | cache and its B-tree | `S/cache/*.go`, k8s `utils/third_party/forked/golang/btree` | cache 107, btree 51 | |
| R2 | 1 | raft core: `raft` (Step, step*, become*, campaign, send*, maybe*, ...), tracing | `S/raft/raft.go`, `S/raft/{tracing,logger}.go` | raft__*, step*, newRaft, trace*, ... (~90) | |
| R3 | 1 | raft log: `raftLog`, `unstable`, `readOnly`, util | `S/raft/{log,log_unstable,read_only,util}.go` | raftLog, unstable, readOnly, ... (~60) | |
| 2a | 2 | gRPC server handlers (KV, lease, auth, maintenance, cluster), interceptors, error mapping; **grpc and proto boundary** | `S/server/etcdserver/api/v3rpc/*.go` except watch.go; `api/v3/v3rpc/rpctypes` | v3rpc (~70), rpctypes 4 | |
| 2b | 2 | gRPC watch server | `S/server/etcdserver/api/v3rpc/watch.go` | ~18 | |
| 2c | 2 | server request path: `v3_server.go` (Put/Range/Txn/DeleteRange/Compact/Lease*/Auth*, raftRequest, processInternalRaftRequestOnce, linearizable reads), read-index loop; `pkg/v3/{wait,idutil,notify}` | `S/server/etcdserver/v3_server.go`, `etcdserver/read/`, `S/pkg/{wait,idutil,notify}/` | ~40 + read 9 + 16 | |
| 2d | 2 | server apply thread and raft node: `run`, `applyAll`, `applySnapshot`, `applyEntries`, `applyEntryNormal`, `applyConfChange`, snapshots, `raftNode`; cindex; schedule | `S/server/etcdserver/{server,raft,snapshot_merge}.go` (apply/raft parts), `etcdserver/cindex/`, `S/pkg/schedule/` | ~80 + cindex 8 + 10 | |
| 2e | 2 | server bootstrap, storage, stop: `NewServer`, `bootstrap*`, storage (WAL, snap), membership, v2stats, compactor, alarm, election/lock, config, features, leasehttp | `S/server/etcdserver/{bootstrap,storage,corrupt,util,interface,tracing,metrics}.go`, `server.go`'s start/stop, `etcdserver/api/{membership,snap,v2stats,v3compactor,v3alarm,v3election,v3lock}`, `server/storage/*.go`, `server/storage/wal/`, `server/config`, `server/features` | ~100 | |
| 2f | 2 | rafthttp | `S/server/etcdserver/api/rafthttp/*.go` | 93 | |
| R4 | 2 | raft tracker, quorum, confchange | `S/raft/{tracker,quorum,confchange}/*.go` | 31 + 7 + 22 | |
| 3a | 3 | apply (uber applier, auth applier, backends) | `S/server/etcdserver/apply/*.go` | 72 | |
| 3b | 3 | txn (Range/Put/DeleteRange/Txn over mvcc) | `S/server/etcdserver/txn/*.go` | 47 | |
| 3c | 3 | lease (lessor) | `S/server/lease/*.go`, `lease/leasehttp` | 39 + 1 | |
| 3d | 3 | auth (store, simple token) | `S/server/auth/*.go` | 54 | |
| 3e | 3 | mvcc core: store, txns, index, keyIndex, revision, compaction, hash, kv views | `S/server/storage/mvcc/{kvstore,kvstore_txn,kvstore_compaction,index,key_index,revision,store,hash,kv,kv_view,metrics_txn,metrics}.go` | ~95 | |
| 3f | 3 | mvcc watch: watchable store, watcher, watcher group; `pkg/v3/adt` | `S/server/storage/mvcc/{watchable_store,watchable_store_txn,watcher,watcher_group}.go`, `S/pkg/adt/` | ~47 + 41 | |
| 3h | 3 | protobuf messages: raftpb, etcdserverpb, mvccpb/authpb helpers, api/v3 version | `S/raft/raftpb/`, `S/api/etcdserverpb/`, `S/api/{mvccpb,authpb,version}/` | 57 + 84 + 2 | |
| 4a | 4 | backend | `S/server/storage/backend/*.go` | 91 | |
| 4b | 4 | schema; pkg leaves (`traceutil`, `pbutil`, `ioutil`, `httputil`) | `S/server/storage/schema/*.go`, `S/pkg/{traceutil,pbutil,ioutil,httputil}/` | 34 + ~25 | |
| 4c | 4 | bbolt public API (DB, Tx, Bucket, Cursor) | `S/bbolt/*.go` | 135 | |
| 4d | 4 | bbolt internals (`internal/common`, `internal/freelist`) | `S/bbolt/internal/{common,freelist}/*.go` | 83 + 14 | |
| I | 5 | integration: every sketch re-checked against its callees' final specs | all | | |

## Batch notes

Each batch's author records here (under its id) what it decided that others need to know: the
predicates it exports, the open questions for the user, what it left out and why.
