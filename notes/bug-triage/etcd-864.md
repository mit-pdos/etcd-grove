# etcd-io/etcd#864: 0.4.2: term #18446744073709551615

<https://github.com/etcd-io/etcd/issues/864>. Closed 2014-10-25, label `type/bug`, against etcd
0.4.2. There is no code fix. It was closed after CoreOS stopped setting `ETCD_NAME=default`.

**The report.** An etcd 0.4.2 node logged "term #18446744073709551615 started" (`2^64 − 1`).
The maintainers explained that this term is not corruption. etcd 0.4's peer-removal path used
the maximum term as a hack to deny a removed machine (go-raft era, peer and standby modes). The
removal itself happened because, after a reboot, systemd started etcd before cloud-config had
written its environment. The machine came up under the default name `default`, was treated as
a new peer, and the cluster auto-removed it.

## Classification

**N** (misconfiguration and OS packaging), secondary **O-pkg**. The decisive fact: the
behavior is a deliberate sentinel in etcd 0.4's own raft integration (`goraft/raft`, peer and
standby mode), triggered by a node started with the wrong name. etcd 0.4's code, including its
raft library, was replaced in etcd 2.0 by the `raft` package that became etcd-io/raft. None of
it exists at the pins (etcd `107edf7e4`, raft `509271dac`), and nothing in `Code/` corresponds
to peer and standby modes or to auto-removal.

## Notes

- At the raft pin, `Term` is a plain `uint64` that only grows by one per campaign or by
  adopting a message's term. No code writes a sentinel term. The specs treat the term as a
  `w64` in `NState`, and the protocol model's terms are compared as integers. No result here is
  about a term near `2^64`, and none is needed for real runs.
- The underlying hazard, a member restarted under the wrong identity, has a modern relative
  in the batch: a process rejoining under an ID with a different data directory
  (`join-fresh-identity`, raft#197 and etcd#21178). Here, though, the wrong name made etcd 0.4
  treat the node as a new machine, and its removal was the intended reaction.

## Proposal

None (class N, code long gone).
