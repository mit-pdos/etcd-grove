---
upstream: none
checked: 2026-11-03
links: []
blocks-proof: no
---

# etcd: a `--heartbeat-interval` near 2^64 / 5 ms passes validation and crashes etcd at startup

`Config.Validate` checks that the election timeout is at least five heartbeat intervals with
`5*cfg.TickMs > cfg.ElectionMs` in `uint` arithmetic, which wraps. With
`--heartbeat-interval=3689348814741910324 --election-timeout=1000`, `5 × 3689348814741910324` wraps
to `4`, so `Validate` accepts the pair; the election timeout in ticks (`ElectionMs / TickMs`) is then
`0`, and raft's `StartNode` panics on the invalid configuration ("election tick must be greater than
heartbeat tick", `node.go:256`). The heartbeat itself (`time.Duration(TickMs) * time.Millisecond`,
`bootstrap.go:563`) also wraps: at `TickMs = 2^58` it is 0 (the ticker never fires), and above
`2^63 / 10^6` it can be negative (`time.NewTicker` panics).

**Why not an issue:** an absurd configuration (a heartbeat interval of about 10^8 years); the
validation failure is a crash at startup, not a wrong result. Found while repairing `bootCfgOk`
(the whole-`bootOk` review's S2, 2026-11-03), whose restatement (proposed, branch `boot-premises`)
has `bootstrap`'s contracts state the heartbeat Go computes and `NewServer`'s specs take the exact
Go condition on it (positive, `int64`, wrapping) as a premise.

`TestHeartbeatIntervalWrap` in
[`nonissues/etcd-heartbeat-interval-wrap/heartbeat_wrap_test.go`](etcd-heartbeat-interval-wrap/heartbeat_wrap_test.go),
copied into `server/embed` at the fork's `323320bb8` (`etc/goose.py`'s pin; the check is the same at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef, `server/embed/config.go:987`), go1.27.3:

```
--- FAIL: TestHeartbeatIntervalWrap (0.00s)
    zz_hb_wrap_test.go:16: Validate accepted --heartbeat-interval=3689348814741910324 --election-timeout=1000 (ElectionTicks 0)
```

The heartbeat's wrap is measured by `TestSpecBootstrapHeartbeat` (`etc/spec-test/bootstrap/`).

## Proof

no: the examples' configuration (`TickMs = 100`, `ElectionTicks = 10`) is far from the wrap;
`bootCfgOk` (`InvBoot.lean`) requires `1 < ElectionTicks`, and (as restated, S2) `NewServer.spec`
the heartbeat `TickMs * 10^6` (as `int64`, wrapping) positive.

## Notes

The fix is to compare without overflow (`cfg.TickMs > cfg.ElectionMs/5`) and to bound `TickMs` so
that the heartbeat fits a `time.Duration`.
