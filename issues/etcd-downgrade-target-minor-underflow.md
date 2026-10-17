---
upstream: unchecked
checked: 2026-10-16
links:
---

# server: at a cluster version x.0 the allowed downgrade target is x.18446744073709551615

- **Status**: bug (a wrong result; since the move to `github.com/Masterminds/semver/v3`, whose
  `Minor()` is a `uint64`; with coreos go-semver's `int64` the target was `x.-1`, which matches no
  parsed version).
- **Where**: `server/etcdserver/version/downgrade.go:57-60` at the pinned revision (`etc/goose.py`,
  etcd 09669450f), the same on upstream `main` (b25719d10):

  ```go
  func allowedDowngradeVersion(ver *semver.Version) *semver.Version {
  	return semver.New(ver.Major(), ver.Minor()-1, 0, "", "")
  }
  ```
- **What happens**: for a cluster version with minor 0 (3.0 is `MinClusterVersion`, which the
  monitor's `decideClusterVersion` returns while a member's version is unknown,
  `version/monitor.go:75`), `Minor()-1` wraps, and `Manager.DowngradeValidate` accepts the target
  `3.18446744073709551615` (`VALIDATE` returns success; `ENABLE` would record it as the downgrade
  target). Reproduction: `notes/pr-verify/etcd-22575/version/downgrade_underflow_test.go`
  (`cp <file> server/etcdserver/version/ && go test -run TestDowngradeValidateAtMinorZero
  ./etcdserver/version/`): fails on 09669450f, on the fork with etcd-io/etcd#22575 and on upstream
  `main` (`version/test-*.log` there); `notes/pr-verify/etcd-22575/review_downgrade_test.go`
  (`TestReviewDowngradeTargetUnderflow`) shows it through `EtcdServer.Downgrade`. Not reproduced: the
  effect of such an enabled downgrade on the version monitor (by code reading, `decideClusterVersion`
  would then reject every member's version as an invalid downgrade until it is cancelled).
- **Expected**: no allowed target below x.0 (`ErrInvalidDowngradeTargetVersion` for every target),
  as the Todo next to it says for major-version downgrades.
- **How the proof handles it**: not excluded: the specs on `pr-verify/etcd-22575`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/version/allowedDowngradeVersion.lean`) state only that
  the result is not `nil`, and the semver postulates say nothing of the values.
- **Possible fixes**: `if ver.Minor() == 0 { return nil }` (with `DowngradeValidate` rejecting a `nil`
  allowed target), or compare with a signed minor.
- **Found**: 2026-10-16, the reviewer of the etcd-io/etcd#22575 verification.
