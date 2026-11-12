---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# embed: a `--raft-read-timeout` below 3ns makes every stream writer panic

`embed`'s flag `--raft-read-timeout` writes the global `rafthttp.ConnReadTimeout`
(`embed/config.go:631`). `etcdmain` clamps it to at least the 5s default
(`etcdmain/config.go:180-187`), but a program that configures `embed` directly does not. Each
`streamWriter.run` calls `time.NewTicker(ConnReadTimeout / 3)` (`stream.go:169`). For a timeout
below 3ns the period is 0 or negative, and `NewTicker` panics on the writer's goroutine, which
ends the process.

**Why not an issue:** no test; found by code reading (2f's round-1 completeness review). It needs
an absurd configuration (a read timeout of nanoseconds), which etcd's own binary clamps away.

## Proof

no: rafthttp's `vars_init.spec` states the scope, that no one writes the timeouts after
initialization (they stay at least 5s), which etcdmain meets.

## Notes

A fix: clamp in `embed` as `etcdmain` does, or validate the flag in `Config.Validate`.
