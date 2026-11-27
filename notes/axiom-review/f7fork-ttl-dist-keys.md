# `Lease_TimeToLiveOn_dist`: the reply-keys conjunct (delta review, 2026-11-26)

**Verdict: SOUND** (the delta). One optional docstring nit, no change to the statement.

Axiom `Lease_TimeToLiveOn_dist.wp_proof : Lease_TimeToLiveOn_dist.spec`, spec file
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/LeaseTimeToLiveOnDist.lean`, branch
`etcd-safe-f7-fork/2026-11-26` (worktree at `059eaf26f0`). Delta reviewed: `git diff c5b8bb0348` of that file. The
statement's only change is the success arm's new conjunct

```lean
(if leaseKeysFold gs false then
  iprop(∃ (ks : GoSlice) (kbs : List GoSlice) (kss : List (List w8)),
    structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"Keys" resp ↦□ ks ∗
    ks ↦*□ kbs ∗ ([∗list] kb;k ∈ kbs;kss, kb ↦*□ k) ∗
    leaseCheckD (Γ.au mid) (principalOf cfg) n
      (fun info => [∗list] k ∈ kss,
        auth.permVerdictFrom (.on (Γ.au mid)) n info k [] .read GoInterface.nil))
 else iprop(True))
```

with the same `n` (`n₀ ≤ n`, `authPubLbM n`) as the existing keys verdict. The rest was reviewed before
(`f7-c.md`, `f7-rerev-c.md`, `f7-getOn-n1.md`) and is considered only where it meets the conjunct.

Go code: etcd fork `/shared/etcd-fork-ttlkeys` at `d26dd5da6`; grpc `v1.84.0` and protobuf-go `v1.36.12`
(`client/v3/go.mod:17-18`, `server/go.mod:41-42`); toolchain go1.27.3. The server side of the claim (the in-process
`EtcdServer.LeaseTimeToLive.spec` keys conjunct, over `checkLeaseTimeToLiveKeys` and the owned-keys contract) is
proved or reviewed SOUND (`f7fork-leasettl-keys-contract.md`); this review covers the transfer to the client.

## Claims

1. `resp.Keys` (the client's `*LeaseTimeToLiveResponse`) is the slice `ks`, its `len` cells the slices `kbs`, each
   holding the bytes `kss`, all persistently (nobody writes them after `TimeToLive` returns).
2. `kss` are exactly the keys member `mid` checked, and the check passed in one of `leaseCheckD`'s arms: auth
   disabled at a state of index `≥ n`; or an `info` with `P = some info.Username'` that is admin, or for which every
   key is read-permitted (`permVerdictFrom … n`).

## Probe 1: the client's `Keys` aliasing the `pb` response

`client/v3/lease.go:246-261`: `resp` (the `*pb.LeaseTimeToLiveResponse` from `l.remote.LeaseTimeToLive`) is a local;
`gresp` is a fresh literal whose `Keys` is `resp.Keys` and whose `ResponseHeader` is `resp.GetHeader()` (another
object). `resp` itself is then dropped: nothing in `lessor` or the interceptors stores it. The unary interceptors
(`retry_interceptor.go:43-64`) pass `reply` to `invoker` synchronously, possibly several times (retries); each
decode is `proto.Unmarshal` (no `Merge`), which resets the message first, so the last successful attempt's keys are
fresh, and no goroutine of a failed attempt holds `reply` (grpc's `RecvMsg` decodes in the caller's goroutine). So
`gresp.Keys`, its array and the key arrays are reachable only from the caller. Giving them as `↦□` is the caller's
weakening of ownership (as the existing `ID ↦□ id`): true.

## Probe 2: grpc's pooled receive buffers

grpc v1.84 `encoding/proto/proto.go`, `codecV2.Unmarshal`: `buf := data.MaterializeToBuffer(mem.DefaultBufferPool());
defer buf.Free(); return proto.Unmarshal(buf.ReadOnlyData(), vv)`: the buffer goes back to the pool when `Unmarshal`
returns, and is reused by later calls. That is harmless because protobuf-go copies every repeated `bytes` element:
`Keys` is `bytes,5,rep,proto3` (`api/etcdserverpb/rpc.pb.go:2957`, protoc-gen-go v1.36.12, no generated
`Unmarshal`), decoded by `consumeBytesSlice` (`internal/impl/codec_gen.go:5568-5580`: `append(emptyBuf[:], v...)`,
whatever `AliasBuffer`, which `proto.Unmarshal` never sets). An empty key is `emptyBuf[:]` (len 0, cap 0, shared by
every empty key: owns no byte; persistent anyway here). No codec is overridden in the client (`ForceCodec`,
`RegisterCodec`, `CallContentSubtype`: none in `client/`, `api/`).

Test (below): 4000 `TimeToLive` calls from 8 goroutines through the real `clientv3.New` client and a real grpc
server, every reply of equal size (so the pool's buffers are reused), half of them overwriting their own keys:
no earlier reply's keys changed, no two non-empty keys share an array, every empty key has cap 0; `-race` clean.

## Probe 3: the index `n`

`permVerdictFrom (.on γa) n info k [] .read nil` says: at some recorded state of index `≥ n` the key is permitted to
`info`, and at some (possibly other) state of index `≥ n` auth is off or `st.revision ≤ info.rev`. The keys check
(`v3_server.go:719-725`) runs after `requireAuthInfo` and `checkLeaseTimeToLive` at the same member, so every state
it reads has index `≥` the published index `n` the existing conjuncts already use (`n = n₀` would do: `authPubLbM n₀`
is in the pre and the member's applied index only grows). The claim is member-local: a grant revoked by an entry the
leader has committed but `mid` has not applied passes `IsRangePermitted` at `mid`, and the conjunct says only that
`mid`'s state at some index `≥ n` permitted it, which is what happened. Nothing in the delta lets a client infer
permission at a later index or at another member. True. The two `leaseCheckD`s (existing and new) are separate
existentials (separate `AuthInfoFromCtx` calls, `checkLeaseTimeToLive`'s and `checkLeaseTimeToLiveKeys`'s), each
true at its own time; nothing ties their arms, so no contradiction (e.g. admin in one, auth-off in the other, if
auth was disabled between: both true).

## Probe 4: the admin arm and auth disabled

`checkLeaseTimeToLiveKeys` (`v3_server.go:735-757`): `!IsAuthEnabled()` → nil without a check: `leaseCheckD`'s
`enabledVerdictFrom … n false` arm (the flag read false at index `≥ n`). `IsAdminPermitted(authInfo) == nil` → nil
without a per-key check: the `adminVerdictFrom … n info nil` arm, with `info` the second `AuthInfoFromCtx`'s, whose
user is the principal by the same token argument as the existing conjunct (`outTokOk`; an invalid or expired token
is an error, `ErrInvalidAuthToken`, not a different user). In both arms the conjunct claims nothing per key, so
nothing false.

## Other cases

- **`leaseKeysFold gs false = false`**: `True`; nothing claimed (the server leaves `Keys` nil).
- **Keys requested, lease not found** (at the leader, or forwarded): `leaseTimeToLive` returns `ErrLeaseNotFound`
  before the keys check, and v3rpc (`api/v3rpc/lease.go:62-76`) turns it into a success with `TTL: -1` and no keys.
  The client decodes `Keys == nil`: `kss = []`, the `[∗list]` is `emp`, and `leaseCheckD … (fun _ => emp)` follows
  from the existing conjunct's `leaseCheckD` (monotone in `K`), i.e. from `checkLeaseTimeToLive`'s passed check. True.
- **Empty lease** (`len(ks) = 0`): the server's `make([][]byte, 0)` is encoded as nothing, decoded as `nil`; same.
- **Error arms**: unchanged (`resp = null`); a check failure (`ErrPermissionDenied`, `ErrAuthOldRevision`, ...) is an
  error arm.
- **v3rpc between the check and the wire**: `ls.hdr.fill(resp.Header)` only; the server's interceptors and grpc's
  marshal only read. The bytes the client decodes are the bytes checked.

## Not tried

A Lean counterexample (no gap found to build one on).

## Tests

`notes/axiom-review/f7fork-ttl-dist-keys-gotest/ttl_keys_client_test.go` (`TestF7forkTTLKeys`), run in a copy of the
fork's `client/v3` with `../pkg` and `../../api` beside it (broken symlinks of the copy removed):
`GOTOOLCHAIN=go1.27.3 go test -count=1 -race -run TestF7forkTTLKeys -v .` (grpc v1.84.0, protobuf v1.36.12):

```
=== RUN   TestF7forkTTLKeys
    ttl_keys_client_test.go:138: replies 4000, non-empty keys 32000, changed 0, shared starts 0, empty keys 4000 (cap>0: 0)
--- PASS: TestF7forkTTLKeys (0.43s)
PASS
ok  	go.etcd.io/etcd/client/v3	1.467s
```

## Nit (docstring only, optional)

"each readable (`IsRangePermitted(k, [])`) by the caller's principal at member `mid`'s applied auth state at an index
`≥ n`" reads as one state; `permVerdictFrom` is two recorded states (the permission, and the revision/auth-off read),
each at an index `≥ n`. Suggested: "each readable (`IsRangePermitted(k, [])`, `permVerdictFrom`) by the caller's
principal at states of member `mid`'s auth store of index `≥ n`".
