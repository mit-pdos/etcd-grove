---
upstream: unchecked
---

# The startup log's `auto-compaction-interval` field prints the retention

- **Status**: a wrong log field (cosmetic, but misleading now that etcd-io/etcd#18472 proposes a
  real `--auto-compaction-interval` flag).
- **Where**: `server/embed/etcd.go:367` at the pinned revision (`upamanyus/etcd` `09669450f`, the
  same code as upstream `main`; present since `3ac4d208a`, 2018), in `print`'s "starting an etcd
  server" log:
  `zap.String("auto-compaction-interval", sc.AutoCompactionRetention.String())`.
- **What happens**: the field named `auto-compaction-interval` holds the retention
  (`--auto-compaction-retention`), the same value as the `auto-compaction-retention` field two
  lines above. Nothing in etcd is called the auto-compaction interval at this revision; with
  etcd#18472 (which leaves this line unchanged) the log would show the retention under the new
  flag's name, not the configured interval. (By reading; no test.)
- **Expected**: the field shows the compaction interval, or does not exist.
- **How the proof handles it**: not at all: `embed` is not translated.
- **Possible fixes**: drop the field, or (with etcd#18472) log `sc.AutoCompactionInterval`.
- **Found**: 2026-10-17, by the review of etcd#18472's verification (branch
  `pr-verify/etcd-18472`).
