# etcd's test bridge, vendored

`tests/framework/integration/bridge.go` of etcd at the fork's pin (`upamanyus/etcd` `8a24be2a3`,
`etc/goose.py`'s etcd revision; the file is upstream's, unchanged by the fork): the TCP proxy
etcd's integration tests put between a client and a member (`ClusterConfig.UseBridge`), with
`Blackhole`/`Unblackhole`, `DropConnections` and `PauseConnections`/`UnpauseConnections`
(`notes/client-cut-plan.md`, D-C1). `LICENSE` is etcd's (Apache 2.0).

## The changes

- `bridge.go`: the package clause only (`package integration` -> `package bridge`); the file is
  otherwise byte-for-byte upstream's.
- `dialer.go` (new): etcd builds a bridge with the unexported `newBridge` and its `dialer` type
  (`tests/framework/integration/cluster.go`, `dialer` and `Member.listenGRPC`), so this copy adds
  that `dialer`, copied, and an exported `New(addr, l)` over the two.
- `bridge_test.go` (new): `TestBlackholeTwicePanics`, the reproduction of
  `issues/nonissues/etcd-bridge-blackhole-twice-panic.md` (a second `Blackhole` panics). Goose does not
  translate test files.
