---
upstream: unchecked
links:
  - etcd-io/etcd#22476 pr open: replaces these loops' time.After with time.NewTicker, which turns the busy loop into a panic at startup (notes/pr-verify/etcd-22476.md)
---

# server: a negative `--downgrade-check-time` or gateway `--retry-delay` is accepted, and its monitor loop spins

- **Status**: a missing configuration check (minor: a CPU-spinning loop on a misconfiguration;
  not in the verified code, found while verifying etcd-io/etcd#22476).
- **Where**: at 09669450f (`etc/goose.py`'s etcd pin):
  - `server/etcdserver/server.go:2332-2350`, `EtcdServer.monitorDowngrade`: `t :=
    s.Cfg.DowngradeCheckTime; if t == 0 { return }`, then `for { select { case <-time.After(t): ...
    } }`. The flag `--downgrade-check-time` (`server/embed/config.go:742`) is not validated
    (`Config.Validate` checks `--compact-hash-check-time` only, `config.go:1022-1024`).
  - `server/proxy/tcpproxy/userspace.go:196-224`, `TCPProxy.runMonitor`: `case
    <-time.After(tp.MonitorInterval)`; `Run` replaces only `0` with its default (line 74); `etcd
    gateway start --retry-delay` (`server/etcdmain/gateway.go:77`) is not validated.
- **What happens**: with a negative duration `time.After` fires at once, so each loop runs
  continuously: on the leader, `monitorDowngrade` calls `CancelDowngradeIfNeeded` (which reads the
  cluster's downgrade state) in a tight loop; the gateway's monitor takes `tp.mu` and starts a
  reactivation goroutine per inactive endpoint in a tight loop. Reproduction: the base-revision runs
  of `notes/pr-verify/etcd-22476/monitor_interval_test.go` and `userspace_monitor_test.go` pass
  (the loops spin until stopped); with etcd-io/etcd#22476 applied they panic instead
  (`notes/pr-verify/etcd-22476/negative-interval.log`).
- **Expected**: a negative interval rejected at configuration time (as `--compact-hash-check-time`
  is), or treated as `0`.
- **How the proof handles it**: not verified (neither function is translated with a body; the
  server's `.toml` translates the apply thread and the request path only). `time.NewTicker`'s spec
  here (`Spec/time/NewTicker.lean`) takes `0 < d`: a proof of either loop over `NewTicker` would
  need the check as a premise.
- **Possible fixes**: validate both flags (`> 0`, or `>= 0` with `0` meaning disabled / the
  default), in `embed.Config.Validate` and the gateway's start.
- **Found**: 2026-10-17, verifying etcd-io/etcd#22476 (its tickers' `NewTicker` precondition).
