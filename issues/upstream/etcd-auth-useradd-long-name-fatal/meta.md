# etcd-auth-useradd-long-name-fatal

- **Finding**: `issues/etcd-auth-useradd-long-name-fatal.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-auth-useradd-long-name-fatal` in `~/etcd-fixes/etcd-auth-useradd-long-name-fatal`, two commits
  (2026-10-23): 5a3373080 adds the tests, which fail there; 612320b8e is the fix. Not pushed.
- **Base**: upstream `main` 3aaab3479b6c4f5fe1b2b8f33437093c2caae88a (2026-10-23; `UserAdd`/`RoleAdd` and
  `batchTx.unsafePut` as at the pin 09669450f the finding cites)
- **State**: draft

Commit messages (drafts for the user to rewrite):

- `tests: test adding a user or role with a too long name` (no body; `tests:` is the prefix of `tests/common`'s history)
- `server/auth: reject user and role names longer than the max key size`, body: "Such a name became a bbolt key
  larger than bbolt accepts, and the failed write made every member exit while applying the request."

## Security-report rule

Not a security report, the user's standing guidance: etcd trusts its clients, so a crash that a client allowed to
send the request can cause is robustness, not security. `UserAdd`/`RoleAdd` need the root role when auth is
enabled; with auth disabled every client is trusted by configuration. Public candidate.

## Duplicates checked (2026-10-23)

Five searches of etcd-io/etcd: `"key too large"` (0 hits), `"failed to write to a bucket"` (0), `user name length`
(71, titles scanned, none about name length), `role name too long` (29, none), `MaxKeySize` (0). No duplicate, no
open PR. Related: #10907 (merged; added `RoleAdd`'s empty-name check, no length bound).

## Why the fix works

At the base, `authStore.UserAdd` (and `RoleAdd`) runs at apply time on every member: it checks `len(r.Name) == 0`,
then `UnsafePutUser` writes the key `[]byte(r.Name)` to the `authUsers` bucket; bbolt's `Put` returns
`ErrKeyTooLarge` for a key over `MaxKeySize` (32768, the bound is `len(key) > MaxKeySize`), and
`batchTx.unsafePut` calls `lg.Fatal` on any `Put` error. The entry is committed, so every member applies it and
exits, and on restart replays it from the WAL and exits again. With the fix the same function returns
`ErrUserNameTooLong`/`ErrRoleNameTooLong` before opening the transaction, as for an empty name: nothing is written,
the client gets the error, and the members keep running. The bound is exactly bbolt's: 32768 bytes still succeed
(run below).

The test is the issue's example through `tests/common` (runs under both the integration and e2e frameworks): the
same `RoleAdd`/`UserAdd` call the package already makes with an empty name, with a 32769-byte name; nothing else
set, auth disabled (the default), so it is an ordinary request, not a misuse.

## Verification (go1.27.3 linux/amd64)

- At the tests commit 5a3373080 (server code = base): `cd tests && go test -tags integration ./common/ -run
  'TestRoleAdd_Error$' -count=1 -v`: the binary exits, `FATAL m0 failed to write to a bucket {"member": "m0",
  "bucket-name": "authRoles", "error": "key too large"}`, `FAIL go.etcd.io/etcd/tests/v3/common 0.263s`.
  `-run 'TestUserAdd_Simple$'`: passes `NoTLS/empty_username_not_allowed`, then on
  `NoTLS/username_longer_than_max_key_size_not_allowed` `FATAL ... "bucket-name": "authUsers", "error": "key too
  large"`, FAIL. Without `-v` the output is a bare `FAIL` (the member's log is buffered in the exited binary).
- e2e at the base (base `etcd` in `bin/`, `go test -tags e2e ./common/ -run 'TestRoleAdd_Error$'`): fails at
  `role_test.go:64`, etcdctl exit code 1, error does not contain "role name".
- At the fix commit 612320b8e: `go test -tags integration ./common/ -run 'TestRoleAdd_Error$|TestUserAdd_Simple$'
  -count=1 -v` ok (all 15 subtests); the same with `-tags e2e` after `make build` ok (42 s). The client sees
  `rpc error: code = Unknown desc = auth: role name is too long` (and `user name`).
  `cd server && go test ./auth/ ./etcdserver/apply/ ./etcdserver/api/v3rpc/ -count=1` ok. `gofmt -l` empty;
  `go vet ./auth` (server) and `go vet -tags integration|e2e ./common/` (tests) clean.
- Binaries (`go build` in `server/` and `etcdctl/`, GitSHA 3aaab3479), three members on localhost, defaults
  (`/tmp/authlong-scripts/repro.sh`, the finding's script with `role add`): at the base, 32768 bytes `Role ...
  created`, 32769 bytes `Unavailable ... EOF`, all three log the fatal line and exit; after restarting all three,
  each logs it again (2 fatal lines per log) and health fails (the outputs in `issue.md`, pasted from this run).
  With `etcd` built at 612320b8e: 32769 bytes gives `Unknown desc = auth: role name is too long`, all three stay
  healthy.
- Recovery: the base's crashed data directories restarted with the fixed `etcd` (`recover.sh`): no fatal line, all
  three healthy, the 32768-byte role listed; the logged 32769-byte entry is applied as an error.

Not run: the whole `tests/common` and `tests/integration` suites, `make verify` (golangci-lint).

## Review (2026-10-23, by hand)

- Other writes keyed by a name: `UserChangePassword`, `UserGrantRole`, `UserRevokeRole`, `RoleGrantPermission`,
  `RoleRevokePermission`, `UserDelete`, `RoleDelete` first look up the user or role, which exists only with a name
  that passed `UserAdd`/`RoleAdd`, so they write back an existing key; `UserGrantRole` with a too-long role name
  gets `ErrRoleNotFound`. Permission keys are stored inside the role's value, not as bbolt keys. No other path
  writes a user or role key.
- Mixed-version clusters: fixed members answer with the error, unfixed members still exit on the entry; state does
  not diverge (the error writes nothing). Upgrading the members recovers a cluster already down (run above).
- No comment or doc claims the old behavior; no doc states a name length bound (none to update).
- No new bug found.

## If a reviewer asks

- Why in `authStore` (apply time) and not in `EtcdServer.UserAdd`/`RoleAdd` before proposing: the empty-name check
  is there, and apply time is the only place every path goes through, including an entry already in a WAL (from an
  unfixed member, or a cluster already down): a check before proposing alone would leave such a cluster unable to
  restart. A check before proposing could be added too, to keep the entry out of the log; not done, to keep the
  change minimal.
- Why `bolt.MaxKeySize` in `server/auth` (a new import of bbolt there): it is the exact bound the write fails at,
  and `server` already depends on bbolt. Alternatives: a constant in `server/auth` (restates bbolt's), or a check in
  `schema.UnsafePutUser`/`UnsafePutRole` (they return no error; changing the `AuthBatchTx` interface is a larger
  change). A smaller bound (names of a few hundred bytes) would be a behavior change for names that work today.
- gRPC mapping: the new errors are not in `v3rpc`'s `toGRPCErrorMap`, so clients get `codes.Unknown` with the
  message `auth: user name is too long`. Mapping them like `ErrUserEmpty` (`rpctypes.ErrGRPCUserNameTooLong`,
  `InvalidArgument`) is four more lines per error in `api/v3rpc/rpctypes/error.go` and `server/etcdserver/api/v3rpc/
  util.go`, kept out to keep the change minimal (the user's review note); add it if a maintainer asks.
- Backports: `release-3.6`/`release-3.5` not checked or run.
