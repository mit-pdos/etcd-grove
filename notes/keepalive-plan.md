# Plan: keepalive in the client's configuration, and failover on a silent partition

Status: in progress (2026-10-21, branch `keepalive`, worktree `/shared/etcd-grove-ka`): KA0 and KA1
done (D28 approved). Follows
`notes/client-cut-plan.md` (K4, failover; `notes/decisions.md` D27).

## Goal

Production etcd clients configure gRPC keepalive (`Config.DialKeepAliveTime`/`DialKeepAliveTimeout`;
Kubernetes' API server uses 30s and 10s). A member cut off silently (packets dropped, no FIN or
RST) leaves its client connection looking healthy. The keepalive pings go unanswered, grpc closes
the connection after `Timeout`, its calls in flight fail (`Unavailable`), and grpc's round-robin
balancer stops picking it while a re-dial cannot complete: that is how a production client fails
over on a silent partition.

`clientCfgOk` excludes keepalive today (`DialKeepAliveTime ≤ 0`, `Proof/go_etcd_io/etcd/client/
v3/InvClientNew.lean`), so `TestFailover` approximates the keepalive by dropping the blackholed
bridge's connections by hand. This plan:

1. lets `clientv3.New`'s configuration enable keepalive (any `DialKeepAliveTime`,
   `DialKeepAliveTimeout`, `PermitWithoutStream`);
2. gives linkv3p's members the server-side keepalive policy etcd's own `embed` sets, without
   which the server refuses the pings;
3. configures linkv3p's clients with keepalive, so `linkv3p_safe` covers it, and replaces the
   test's hand-made drop with a blackhole alone (a silent partition), with failover after the
   keepalive timeout.

The closed theorem's statement does not change: keepalive only closes connections, which every
call's attempt already allows (an error, nothing said about whether the handler ran).

## What is already there

- **The client's code path.** `Client.dialSetupOpts` (`client/v3/client.go`): if
  `cfg.DialKeepAliveTime > 0`, it builds a `keepalive.ClientParameters{Time, Timeout,
  PermitWithoutStream}` and prepends `grpc.WithKeepaliveParams(params)` to the dial options. Its
  spec takes `DialKeepAliveTime ≤ 0` as a premise, so the branch is never taken in the proof.
  `keepalive.ClientParameters` is already translated, types only (`Code/google_golang_org/grpc/
  keepalive.toml`); `grpc.WithKeepaliveParams` is translated names-only, with no spec.
- **The dial's option descriptors** (`GrpcDialOpt`, `Proof/google_golang_org/grpc/InvDial.lean`):
  `unaryInterceptor`, `streamInterceptor`, `transportCreds`, `resolvers`. A dial option without a
  descriptor (keepalive among them) puts the dial outside `grpc.NewClient`'s axiom.
- **The attempt contract** (`grpcInvokerOk`, `InvGrpc.lean`): an attempt may fail with any client
  error, with nothing said about the handler; the stream specs likewise let a stream's `Recv` and
  `Send` fail at any point (`cliStreamErr`). A connection keepalive closes is one of those.
- **The server side.** grpc's server enforces a keepalive policy: by default a client may ping
  at most once every 5 minutes (`defaultKeepalivePolicyMinTime`), and two pings faster than that
  get a `GOAWAY` (`too_many_pings`) that closes the connection. etcd's `embed` sets
  `grpc.KeepaliveEnforcementPolicy(EnforcementPolicy{MinTime: GRPCKeepAliveMinTime (5s),
  PermitWithoutStream: false})`; our examples build the gRPC server with `v3rpc.Server(s, nil,
  nil)` and no options, so a 10-second client ping would be refused within half a minute.
  `v3rpc.Server`'s spec already takes server options that are `.neutral` (`grpcSrvOpt`,
  `InvGrpcServer.lean`: they do not change which handler runs or what it is given), with axioms of
  that form for `MaxRecvMsgSize`, `MaxConcurrentStreams`, `CustomCodec`, `StatsHandler`.
- **grpc's floor on the ping interval**: `WithKeepaliveParams` raises `Time` below 10 seconds to
  10 seconds (`internal.KeepaliveMinPingTime`). The test's partition must outlast `Time +
  Timeout`.

## Design

**D-KA1. A descriptor for keepalive, and its constructor's axiom.** `GrpcDialOpt` gains
`.keepalive`; `grpc.WithKeepaliveParams(kp)` (a `Spec`/`Proof` pair, an axiom) returns an option
`o` with `grpcDialOptIs o .keepalive`, for any parameters. `unaryIcsOf`, `GrpcDialOpt.streamOf`
and `dialOk` ignore it (it sets no interceptor, no resolver), so `grpc.NewClient`'s axiom covers
dials with it unchanged. What the trust boundary then asserts about keepalive is only that the
option exists and changes no interceptor and no resolver. Its runtime effect, a closed connection, is
inside what `ClientConn.Invoke`'s and `NewStream`'s axioms already allow. Why that is true of
grpc-go: keepalive is transport-level (`http2Client.keepalive`): it sends HTTP/2 pings and, after
`Timeout` without an ACK, closes the transport with a connection error, which fails every stream
on it with `Unavailable`. It never re-sends a request, so an attempt still reaches at most one run
of one handler (D21j). **To be approved by the user**, as D21j and D27 were (a new decision,
D28).

**D-KA2. The server's enforcement policy, a neutral option.** `grpc.KeepaliveEnforcementPolicy(ep)`
gets an axiom returning a `.neutral` server option (it decides when the server closes a
connection, never which handler runs or what it is given; a closed connection is an error for the
client). linkv3p's `startMember` passes `grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy
{MinTime: 5 * time.Second})` to `v3rpc.Server`, as `embed` does with its default. (Server-side
pings, `grpc.KeepaliveParams(ServerParameters{...})`, are not needed: the client's pings detect
the partition. They could be added the same way.) `keepalive.EnforcementPolicy` is already
translated (types).

**D-KA3. The client's configuration.** `clientCfgOk` drops `DialKeepAliveTime ≤ 0`: any keepalive
parameters. `dialSetupOpts`'s spec drops the premise, and its result's descriptors gain a
`.keepalive` first when `DialKeepAliveTime > 0`. `dial`, `dialWithBalancer`, `newClient` and `New`
carry the descriptors through, so they change only in their premises.

**D-KA4. linkv3p's clients with keepalive, and the test.** `newClient` sets `DialKeepAliveTime: 10
* time.Second` and `DialKeepAliveTimeout: 2 * time.Second` (10s is grpc's floor; production
values are larger, which only makes the test slower). `TestFailover` blackholes member 1's bridge
and does nothing else for 15 seconds. Its checks:

- `Ok`;
- the calls in flight on member 1's connection fail after about 12 seconds (keepalive's close);
- after that, every client keeps working: an operation through each, started more than 13 seconds
  into the run and ended before the unblackhole, succeeded.

`TestClientCuts` (one bridge per client) keeps its schedule. With keepalive its blackholed calls
fail after about 12 seconds rather than at the unblackhole, so its blackhole should outlast that, or
its check that some call through client 1 failed already holds earlier. To be measured.

## Stages

### KA0. The Go program

- `startMember`: `v3rpc.Server(s, nil, nil, grpc.KeepaliveEnforcementPolicy(...))`.
- `newClient`: the keepalive parameters.
- `TestFailover` as D-KA4; `TestClientCuts` and `TestMainRun` re-measured; `go test -race`.
- Confirm by a test that, without the enforcement policy, a client with a 10-second keepalive
  gets `GOAWAY too_many_pings` within a minute (the finding behind D-KA2; a note, not an issue:
  it is a configuration of ours, not a bug of etcd's).

**Done (2026-10-21).** `startMember` passes `grpc.KeepaliveEnforcementPolicy(keepalive.EnforcementPolicy
{MinTime: 5 * time.Second})`; `newClient` sets `DialKeepAliveTime: 10s`, `DialKeepAliveTimeout: 2s`
(grpc is now a direct dependency of linkv3p's module). Findings:

- **Without the policy the pings are refused**: a probe (grpc's health service, a client with a
  10-second keepalive, a stream kept open) saw its stream cut after 31s with `GOAWAY
  ENHANCE_YOUR_CALM "too_many_pings"`; with the 5-second policy the stream lived to its 45-second
  deadline. A configuration of ours (etcd's `embed` sets the policy), not an issue.
- **Each client finds the cut member on its own.** A client pings only while it has calls in
  flight (`PermitWithoutStream: false`, which etcd's server requires: its policy counts a ping on
  an idle connection as a strike). A client's idle connection to the blackholed member is not
  probed, and stays READY until a call is sent on it; that call hangs 2 to 12 seconds (2 if the
  connection has not read for 10 seconds already), then fails, and from then on the balancer
  skips it (a re-dial is never READY: grpc waits for the server's preface). So a silent partition
  costs each client one stall, and the workers that picked that client stall with it: in the runs,
  one to three closes, at 12s, 14s to 24s.
- `TestFailover` (blackhole alone, 45s): every failure during the cut ended between 12s and 24s,
  and then each client served thousands of operations through the other two members; 4 runs of 4
  passed (15 to 35 seconds each). `TestClientCuts` (its 3-second blackhole is shorter than the
  keepalive) and `TestMainRun` unchanged. `go test -race` passes.

Until KA2 and KA3, linkv3p's `startMember` and `newClient` proofs do not build (the server option
and the configuration's new fields; the translation and package tables regenerated).

### KA1. The trust boundary (asked of the user)

- `GrpcDialOpt.keepalive`; `Spec/google_golang_org/grpc/WithKeepaliveParams.lean` and its axiom;
  the lemmas that `unaryIcsOf`, `streamOf` and `dialOk` ignore it.
- `Spec/google_golang_org/grpc/KeepaliveEnforcementPolicy.lean` and its axiom (`.neutral`).
- `notes/decisions.md` D28, and ask.

**Done (2026-10-21; D28 approved).** `GrpcDialOpt.keepalive` with `unaryIcsOf_keepalive` and
`dialOk_keepalive` (`InvDial.lean`); `Spec`/`Proof` pairs for `grpc.WithKeepaliveParams` and
`grpc.KeepaliveEnforcementPolicy`.

### KA2. The client

- `dialSetupOpts`: the branch proved (the struct literal, `WithKeepaliveParams`, the append),
  its result `(if 0 < DialKeepAliveTime then [.keepalive] else []) ++ ds ++ [...]`.
- `dial`: `dialOk` and `unaryIcsOf` of the longer list (by the KA1 lemmas).
- `clientCfgOk` without the keepalive conjunct; the pure conjunction's destructurings in
  `newClient` and in every example's configuration proof (one conjunct fewer).

### KA3. linkv3p

- `startMember`'s proof: the server option's slice (`gvs`, `.neutral`) instead of `nil`.
- `newClient`'s proof: the configuration literal's two more fields.
- Gates: `lake build`, every `gen-link` mode, `goose --check`, `gen-init --check`, `tcb-report
  --check` (`--update`: the two new axioms) and every collection, `verified-code.py`.

## Risks

- **The ping floor makes the test slow** (about 15 seconds of partition). Acceptable; the other
  tests stay as they are.
- **Server-side pings and `PermitWithoutStream`.** With `PermitWithoutStream: false` the client
  pings only while calls are in flight, which is the case that matters (a hung call). An idle
  client's dead connection is found at its next call's ping. Not a safety question.
- **Other examples.** Their configurations stay without keepalive; their proofs change only in the
  destructuring of `clientCfgOk`'s pure part.

## Sizing (rough)

- KA0: small. KA1: two small axioms and a decision. KA2: small to medium (`dialSetupOpts`' branch,
  the destructurings). KA3: small.
