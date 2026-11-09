# Requirements on `go.etcd.io/etcd/server/v3/auth` (3d: the auth store, token providers)

## from 2b

Batch 2b (the member's gRPC watch handler) checks each watch create's read permission
(`serverWatchStream.isWatchPermitted`, `watch.go:239`), and the client's watch contract (1b's
`wireStep`) promises that a registered watch's principal **may read its range at a state the
cluster reached** (`σa.permits who [(.read, range)] []`, W0's `Model.lean`). What 2b's sketch
assumes, in plain terms:

1. **`AuthInfoFromCtx(ctx)`** (the auth store's, through `EtcdServer.AuthInfoFromCtx`, 2c), for a
   server-side context whose incoming metadata names the principal `who` (2b's `srvCtxPrin ctx who`,
   2a): `(nil, nil)` (no token), or an `*AuthInfo` whose `Username` is `who`'s user (`who = some u`)
   with its token's auth revision, or an error (an invalid token: `ErrInvalidAuthToken`, ...). No
   panic.
2. **`IsRangePermitted(info, key, rangeEnd)`**, `info` such an `*AuthInfo` or `&AuthInfo{}` (empty
   user, revision `0`), with a thread token (the store's reader lock and backend read
   transaction): `nil` **only if** some state `σa` the cluster reached (`etcdLb γ σa`, the member's
   applied auth state) has auth disabled, or has `info`'s user `u` with the root role or with read
   permission covering every key of `{key, rangeEnd}` (`AuthState.covers u .read`, `KeyRange.mem`:
   an empty `rangeEnd` the single key, `"\x00"` from the key on, as `rangePermCache` reads them);
   i.e. `σa.permits who [(.read, ⟨key, rangeEnd⟩)] []` for the `who` of item 1. Any error
   otherwise (`ErrUserEmpty`, `ErrAuthOldRevision`, `ErrPermissionDenied`). The reads of
   `IsAuthEnabled`, `Revision` and the user need not be atomic: each outcome is justified at one
   reached state (auth off at the first read; else the user read at the transaction's state).
   ```go
   return sws.ag.AuthStore().IsRangePermitted(authInfo, wcr.Key, wcr.RangeEnd)
   ```
3. `errors.Is(err, auth.ErrInvalidAuthToken)` etc. on the returned error: Perennial's `errors`
   (the package's error variables initialized, its `isPkgInit`).

Used by: `serverWatchStream.isWatchPermitted.spec`, hence `srvWireStep`'s registered-`Created`
case; snippet `examples/specreq/v3rpcwatch/protocol.go` (`ReqPermission`).
