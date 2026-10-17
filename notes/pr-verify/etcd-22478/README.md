# etcd-io/etcd#22478: files

| File | What it shows | Revision | Command |
|---|---|---|---|
| `build-pr-head.log` | The PR does not compile: `etcdserver/bootstrap.go:182:13: s.beHooks.lg undefined (cannot refer to unexported field lg)` | PR head `76f956d4e2ba50ef368e10e6fb8e206910d2fe82` (upstream) | `cd server && GOTOOLCHAIN=go1.27.1 go build ./etcdserver/` |
| `build-fork-goose-lean.log` | The same error once the PR is applied to the Goose fork | `mit-pdos/etcd-grove` branch `pr-etcd-22478-goose-lean` (`3aeea6a2a`, PR onto `09669450f`) | the same |

At the PR's merge base with upstream `main` (`7583cc6e7e2756bb4166d646fe48d2fa1863b4b6`) the same
`go build ./etcdserver/` succeeds, so the one changed line is what breaks the build.
