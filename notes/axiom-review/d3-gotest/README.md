# D3 witness: the six admin kinds against the real auth store and protobuf (review rev-d3, 2026-11-28)

Two Go tests from the independent review of nomode D3 (`notes/nomode-n1.md`, "D3").

- `zz_d3rt_test.go.txt`: each of the six requests (`AuthDisable`, `AuthUserDelete`,
  `AuthUserChangePassword`, `AuthUserRevokeRole`, `AuthRoleDelete`, `AuthRoleRevokePermission`) in an
  `InternalRaftRequest` (with and without a header, empty contents, nil and empty `Key`/`RangeEnd`)
  through `proto.Marshal`/`proto.Unmarshal`, compared with `proto.Equal`; invalid UTF-8 in each
  string field. Copy to `api/etcdserverpb/zz_d3rt_test.go`; run `go test ./etcdserverpb -run
  TestD3RoundTrip -v` in `api/`.
- `zz_d3_test.go.txt`: the real `authStore` over the real bbolt backend: 40000-byte names for
  `UserChangePassword`, `UserRevokeRole`, `RoleRevokePermission`, `UserDelete`, `RoleDelete`;
  `UserChangePassword` of a no-password user and of a password user with a non-base64
  `HashedPassword`, an 80-byte plaintext, and empty/empty; `UserRevokeRole` of a role not granted;
  `AuthDisable` while disabled; `UserDelete` while disabled. Copy to `server/zzd3/zz_d3_test.go`; run
  `go test ./zzd3 -run TestLongNames -v` in `server/`.

Checkout: the pinned fork (upamanyus/etcd `18ab647b02`), `GOPROXY=off`, go1.27.1.

Results (2026-11-28): `TestD3RoundTrip` passes: every request round-trips equal (presence and
fields; empty `Key`/`RangeEnd` come back nil, the model's `[]`); every invalid-UTF-8 string makes
`Marshal` fail, and `Unmarshal` of one fails. `TestLongNames` passes; its log:

    roleadd: <nil> rev=2
    useradd: <nil> rev=3
    chpw long: auth: user not found rev=3
    revoke long: auth: user not found rev=3
    revokeperm long: auth: role not found rev=3
    udel long: auth: user not found rev=3
    rdel long: auth: role not found rev=3
    chpw nopassword-user bad b64: <nil> rev=4
    useradd p: <nil> rev=5
    chpw pw-user bad b64: auth: authentication failed, password was given for no password user rev=5
    chpw pw-user 80-byte plaintext: auth: authentication failed, password was given for no password user rev=5
    chpw pw-user empty/empty: <nil> rev=6
    revoke non-granted: auth: role is not granted to the user rev=6
    disable while disabled rev=6
    udel p (disabled): <nil> rev=7

So a long name only meets "not found" (no write, no panic): the name bounds on these kinds were not
needed (dropped, the stored names' bounds taken instead). `UserChangePassword`'s outcome depends on
the stored user's `NoPassword` option and on the request's passwords (`bad b64` fails for a password
user and succeeds for a no-password one; bcrypt refuses an 80-byte plaintext).
