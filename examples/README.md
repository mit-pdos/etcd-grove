# The examples

Programs over the verified code, each with a Go test and (most) a closed Lean result: an adequacy
theorem (`<name>_adequate`: a run never panics, under the result's premises) and its consequence
(`<name>_safe`, or `_porcupine_safe`: the checks the program makes hold). One Go module
(`go.mod`), except `raft/kvwitness`, `bbolt/bank`, `k8s/*` and `lib/lintest`, which have their own. Their
proofs mirror the paths: `{Spec,Proof}/github_com/mit_pdos/etcd_grove/examples/<dir>/`, the
results in its `Results.lean`, the Lean namespace `<layer>_<dir>` (`etcd_cache`).

Moved here from a flat `examples/` on 2026-11-03 (`notes/examples-layout-plan.md`, with the old
names).

## `raft/`: applications on raft (`go.etcd.io/raft/v3`)

| dir | was | what it is | headline result |
|---|---|---|---|
| `raft/kv` | `kv` | a minimal replicated key-value store (Put, Get, Append through the log), checked by porcupine | `raft_kv_porcupine_safe` |
| `raft/kvreconf` | `kvreconf` | the store with snapshots, configuration changes, a lossy network, leadership disruptions, reads by read index | `raft_kvreconf_porcupine_safe` |
| `raft/kvdurable` | `kvdurable` | `kvreconf` made durable: replicas crash and restart from their files | `raft_kvdurable_porcupine_safe` |
| `raft/kvfile` | `durablekv` | `kv` made durable in one file per replica (translated, not yet proved) | – |
| `raft/kvwitness` | `kvwitness` | `kv` with a witness replica (raft with witness support; the part `RaftWitness/`) | `raft_kvwitness_porcupine_safe` |

## `etcd/`: etcd's server and client, members started in-process

| dir | was | what it is | headline result |
|---|---|---|---|
| `etcd/putget` | `putget` | one member, a Put and a Get of its key | `etcd_putget_safe` |
| `etcd/putget3` | `putget3` | `putget` on a three-member cluster | `etcd_putget3_safe` |
| `etcd/compacted` | `putgetc` | `putget` with the auto-compactor on | `etcd_compacted_safe` |
| `etcd/compactwatch` | `compactkv` | rounds of Puts and watches under compaction pressure | `etcd_compactwatch_safe` |
| `etcd/restart` | `restart3` | `putget3` with a member stopped and restarted on its data directory | (in progress) |
| `etcd/watch` | `watchkv` | a prefix watch against concurrent writers: every Put is seen, in order | `etcd_watch_safe` |
| `etcd/cache` | `cachekv` | `watch` read through etcd's cache, its `Get` and progress notifications checked | `etcd_cache_safe` |
| `etcd/lease` | `leasekv` | the client's lease reads (`Leases`, `TimeToLive`) | `etcd_lease_safe` |
| `etcd/leasegrant` | `leasegrant` | a lease granted, then listed: the listing has it (three-member cluster test of amendment (E)'s failure answers) | `etcd_leasegrant_safe` |
| `etcd/leaseexpiry` | -- | a lease of the minimum TTL granted, polled until not found, then listed: the listing does not have it (no proof yet: `notes/lease-expiry-plan.md`) | -- |
| `etcd/auth` | `authkv` | authentication: users, roles, permissions, tokens | (in progress) |
| `etcd/txnlin` | `linkvtxn` | porcupine over the KV API with transactions, as etcd's robustness tester drives it | `etcd_txnlin_safe` |
| `etcd/partition` | `linkv3p` | `txnlin` on three members under network partitions, and a watch | `etcd_partition_safe` |
| `etcd/bugs` | `etcdbugs` | reproductions of bugs found (`issues/`); not translated | – |

## `k8s/`: Kubernetes over etcd

| dir | was | what it is | headline result |
|---|---|---|---|
| `k8s/etcd3` | `k8setcd3` | porcupine over Kubernetes' etcd3 storage backend | `k8s_etcd3_safe` |
| `k8s/daemonset` | `k8sdaemonset` | a DaemonSet controller over an API-server model | – |
| `k8s/compactor` | – | Kubernetes' etcd compactor as API servers run it: five API servers (three compactors of their own, two sharing one) and a writer on one member compacting only at its clients' requests (K3, K4 of `notes/k8s-compactor-plan.md`), and on three members under network partitions, any schedule (`MainPartition`, K6) | `k8s_compactor_safe`, `k8s_compactor_partition_safe` |

## `bbolt/`: bbolt (`go.etcd.io/bbolt`, the fork with its bodies; the part `Bbolt/`)

| dir | was | what it is | headline result |
|---|---|---|---|
| `bbolt/bank` | `bbolttest` | bbolt's top-level test: a bank whose transfers and snapshot reads must be durable and strictly serializable across crashes (porcupine) | (in progress) |

## `lib/`: shared code

| dir | was | what it is |
|---|---|---|
| `lib/etcdstart` | `common` | starting etcd for the `etcd/` examples (a member, its gRPC service, a client) and the watch workload's checks |
| `lib/lintest` | `lintest` | the porcupine driver: concurrent clients, traced operations, a linearizability check (instances `counter`, `logkv*`) |
| `lib/durable` | `durable` | a node's durable state, files read and written whole (the Go side of `durableExt`) |

## `osfs/`: programs over the Linux file extension

| dir | was | what it is |
|---|---|---|
| `osfs/bboltfs` | `bboltfs` | minibolt, the file extension's acceptance test |
| `osfs/crashlog` | `crashlog` | the smallest crash-safe program: a commit flag guarding 8 bytes |

## `goose/`: proof techniques over goose's primitives

| dir | was | what it is | headline result |
|---|---|---|---|
| `goose/prophkv` | (new) | `GetAny` reads a map twice and returns one answer, chosen at random afterwards: a plain logically atomic spec over a prophecy patch (`etc/proph-patches/prophkv/`) | `goose_prophkv_safe` |

`axiomcx/` holds counterexamples to trust-boundary axioms (`notes/axiom-review/`), not examples.

The raft key-value stores repeat their harness (`check.go`, `cluster.go`, `kv.go`): each is a
separately verified package. Sharing it would be a package of its own with its spec (a follow-up
in `notes/examples-layout-plan.md`), not a copy.
