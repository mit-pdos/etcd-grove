---
upstream: unchecked
checked: 2026-10-16
links:
---

# server/etcdserver/version: `Manager.DowngradeCancel` needs a non-nil `GetDowngradeInfo()`

- **Status**: a precondition the API does not state (not reachable with etcd's own `Server`).
- **Where**: `server/etcdserver/version/version.go` at 09669450f: `Manager.DowngradeCancel`
  (`version.go:71-80`) reads `downgradeInfo.Enabled` of `m.s.GetDowngradeInfo()` unchecked
  (line 77), while `DowngradeValidate` (line 53) checks `downgradeInfo != nil` first. The `Server`
  interface (`monitor.go:35-46`) does not say `GetDowngradeInfo` never returns `nil`; etcd's
  adapter does not (`RaftCluster.DowngradeInfo`, `api/membership/cluster.go:801-809`, returns
  `&DowngradeInfo{Enabled: false}` when there is none).
- **What happens**: a `Server` implementation returning `nil` (a test mock) makes
  `DowngradeCancel` panic; `DowngradeValidate` treats the same `nil` as "no downgrade".
- **Expected**: either the interface documents a non-nil result, or `DowngradeCancel` checks it
  as `DowngradeValidate` does.
- **How the proof handles it**: the contract of the manager's server (`version.isServer`,
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/version/Base.lean`, branch `pr-verify/etcd-22589`)
  requires `GetDowngradeInfo()` to return a non-nil pointer the caller owns.
- **Possible fixes**: a comment on `Server.GetDowngradeInfo`, or
  `if downgradeInfo == nil || !downgradeInfo.Enabled` in `DowngradeCancel`.
- **Found**: 2026-10-16, specifying the version manager for etcd-io/etcd#22589 (pr-verify).
