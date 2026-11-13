# Per-string start tokens and aliases: `netAddrFree`, `httpProtoFree`, `backend.pathOwn` (axiom sweep B3-1b)

Reviewed 2026-11-07 by the `axiom` skill (sweep phase 1, Go first), the follow-up of B3-1
([wal-tokens](wal-tokens.md), branch `axiom/waldiralias`), on `axiom/sweep-b3` at `92e61b5070`
(worktree `/shared/etcd-grove-sweep3`). Go at the pins of `examples/go.mod` (etcd server
`github.com/upamanyus/etcd/server/v3@v3.0.0-20261103162249-673da07c8fab`), go1.27.3. **No Lean was
built** (the sweep's rule): the Lean side is a sketch.

B3-1 showed that program start hands out one `walDirFresh d` per **string** of `Ds` under a
string-level `Ds.Nodup`, while two strings name one directory. This review tries the same alias on
the other per-string tokens.

## The statements

| Statement | Where (at `92e61b5070`) | Kind |
|---|---|---|
| `netAddrFree addr` ("no listener of this program or of any other process is, or will be (other than through this token), bound at the address `addr`") | `Proof/net/InvNet.lean:34` (header `:7-14`) | axiom (opaque `IProp`) |
| `netListenerAt l addr` ("bound at `addr` and accepts the connections dialed to `addr`") | `Proof/net/InvNet.lean:44` (header `:15-17`) | axiom (opaque `IProp`) |
| `httpProtoFree addr` | `Proof/net/InvNet.lean:41` | axiom (opaque `IProp`) |
| `addrsUnclaimed e As` | `Proof/runtime/Start.lean:79` | axiom (opaque `Prop`, a hypothesis of every closed theorem) |
| `goose_adequacy_start` (its `As` part: `startRights`' `[∗list] a ∈ As, netAddrFree a ∗ httpProtoFree a` under `hAs : As.Nodup`, `hAsFree : addrsUnclaimed e As`) | `Proof/runtime/Start.lean:92-94,103-121` | axiom |
| `net.Listen.wp_proof` (consumes `netAddrFree addr`, gives `netListenerAt l addr` or an error) | `Proof/net/Listen.lean:27`, spec `Spec/net/Listen.lean:28-33` | axiom |
| `grpc.start` (`netListenerAt lis addr` → `grpcServerAt addr ...`) | `Proof/google_golang_org/grpc/InvGrpcServer.lean:271` | axiom (statement read only; InvGrpc internals not analyzed, owned elsewhere) |
| `grpc.ClientConn.Invoke.wp_proof` (one attempt is "a run of the handler served for the method at one of `addrs`", `grpcInvokerOk conn addrs`) | `Proof/google_golang_org/grpc/ClientConn__Invoke.lean:32` | axiom (statement read only) |
| `http.reserve` (`httpProtoFree a ==∗ httpProtoAt a P ∗ httpProtoOwn a P`), `http.register` | `Proof/net/http/Axioms.lean:39,45` | axioms |
| `backend.pathOwn p` | `Proof/go_etcd_io/etcd/server/v3/storage/backend/InvSnapshot.lean:93` | **opaque, not an axiom**; produced by `bootOk`'s `"Hpath"` (`InvBoot.lean:449`, inside the premise `bootstrapContract`, `:503`) and the DRAFT restart contract; consumed by `os.Rename.wp_proof` (`Proof/os/Rename.lean:32`) through `storage.OpenSnapshotBackend` |

## Verdict

| Statement | Verdict |
|---|---|
| `goose_adequacy_start` (its `As` part), with `addrsUnclaimed`, `netAddrFree`, `netListenerAt` | **Refuted (Go side; Lean sketched, not built).** `As.Nodup` is a fact of strings; `netAddrFree`'s meaning is a fact of socket addresses. `"localhost:24290"` and `"[::1]:24290"` are distinct strings; `net.Listen` succeeds on both (`127.0.0.1:24290` and `[::1]:24290`), and a dial of `"localhost:24290"` reaches the `[::1]` listener. A client of X's address talks to Y. Counterexample `examples/axiomcx/netaddralias`, 30/30 runs panic. |
| `net.Listen.wp_proof` | Its triple holds (an error is allowed); its docstring's "connections dialed to `addr` reach the listener" is the false reading `netListenerAt` carries, but only because start handed out a token for an overlapping string. Repair it together with the start axiom (below). |
| `grpc.start`, `grpc.ClientConn.Invoke.wp_proof` | Not attacked on their own. The false step uses them as stated: they key the server by the address **string** (`grpcServerAt addr`, `grpcInvokerOk conn addrs`), which is right only when strings are socket identities. |
| `httpProtoFree` / `http.reserve` | **Same per-string flaw, not exhibited.** `RoundTrip` needs `httpProtoAt host` of the request's host string, so a protocol reserved for `"localhost:p"` is trusted on a response from the server bound at `[::1]:p`. The only consumer is rafthttp (the members' peer URLs), where a misrouted message hits another cluster's member and its cluster-ID check (`412`) turns it into an error the protocols allow, most likely. Not tried to a panic. The restatement below covers it. |
| `backend.pathOwn` | **Survives as an alias attack** (it reduces to B3-1's WAL alias, or hangs on bbolt's `flock`). **One finding about an unstated environment fact:** the premise `bootstrapContract` depends on the data directory holding no backend file, and no stated environment premise says so (`walDirsAbsent` covers only the WAL). Demonstrated by a Go test, below. Not a refutation: `bootstrapContract` is a premise. |

## The counterexample: `examples/axiomcx/netaddralias`

`netaddralias.go` (package `netaddralias`; tests only, no Goose project). It uses only etcdstart's
proved starters (putget's: `StartServer`, `Serve`, `NewClient`) and the client's `Put`/`Get`:

```go
const (
	AliasAddr = "localhost:24290" // X's client address: net.Listen binds 127.0.0.1:24290
	V6Addr    = "[::1]:24290"     // Y's client address
	peerAddrX = "127.0.0.1:24310" // not served (one-member clusters)
	peerAddrY = "127.0.0.1:24311"
)

func Run(lg *zap.Logger) {
	x, err := etcdstart.StartServer("naa-x", peerAddrX, AliasAddr, lg)   // + Serve(x, AliasAddr)
	y, err := etcdstart.StartServer("naa-y", peerAddrY, V6Addr, lg)      // + Serve(y, V6Addr)
	cy, err := etcdstart.NewClient(V6Addr, lg);    cy.Put(pctx, "k0", "v1")
	cx, err := etcdstart.NewClient(AliasAddr, lg); resp, err := cx.Get(gctx, "k0")
	...
	if len(resp.Kvs) != 0 {
		panic("netaddralias: a Get through X's address returned a key no client of X put")
	}
}
```

(An error from any step returns, as in putget.)

**What Go does** (go1.27.3):
- `net.Listen("tcp", "localhost:24290")` binds only the name's first IPv4 address: `ListenConfig.Listen`'s
  `la := addrs.first(isIPv4)` (`net/dial.go:889`), so it binds `127.0.0.1:24290`.
- `net.Listen("tcp", "[::1]:24290")` binds the IPv6 loopback, a different socket, so it succeeds.
- A dial of `"localhost:24290"` resolves through the hosts file (`127.0.0.1 localhost` and
  `::1 localhost` here). The resolver sorts the addresses by RFC 6724, which puts `::1` first
  (`goLookupIPFiles`, `net/dnsclient_unix.go:627`). The dialer tries the first address's family
  first (`dialParallel`'s primaries, `net/dial.go:553-560`), so it connects to `[::1]:24290`.

grpc's transport and etcd's client dial the endpoint string with the same dialer. So `cx`, the client
of `"localhost:24290"`, talks to Y, and its Get returns Y's `k0`.

**What the proof says.** X's `Serve` consumes `netAddrFree "localhost:24290"`. `net.Listen`
returns `netListenerAt l "localhost:24290"`, and `grpc.start` (through `etcdstart.kv_served`) turns
it into `grpcServerAt "localhost:24290"` with X's KV handlers. `cx`'s calls are answered by the handler
served at one of its endpoint strings (`grpcInvokerOk`). X is a fresh one-member cluster whose KV
store starts empty (`bootstrapContract`), and no client of X puts. So the Get returns no key, and
the `panic` is dead code.

**Tests** (`go test ./axiomcx/netaddralias/ -v`, under `systemd-run --scope -p MemoryMax=32G`; logs
`/shared/tmp/7c-logs/b3-1b-*.log`):

```
=== RUN   TestAliasAddrs
    netaddralias_test.go:28: listen "localhost:24295": bound 127.0.0.1:24295; listen "[::1]:24295": bound [::1]:24295
    netaddralias_test.go:34: dial "localhost:24295": connected to [::1]:24295
--- PASS: TestAliasAddrs (0.00s)
=== RUN   TestRun
    netaddralias_test.go:48: Run panicked: netaddralias: a Get through X's address returned a key no client of X put
--- PASS: TestRun (1.04s)
=== RUN   TestServedBy
    netaddralias_test.go:72: localhost:24290: member 74b711daa2a8e924, k0 present: true
    netaddralias_test.go:72: [::1]:24290: member 74b711daa2a8e924, k0 present: true
    netaddralias_test.go:72: 127.0.0.1:24290: member 472537db55d675e1, k0 present: false
--- PASS: TestServedBy (0.52s)
```

- `TestRun` passes when `Run` panics (recovered on the main goroutine). In separate processes
  (`go test -c`, then the binary run once per process): **20/20** panicked
  (`b3-1b-run20.log`), and **10/10** more (`b3-1b-run10b.log`), plus the first run (`b3-1b-first.log`).
- `TestServedBy` shows which member answers each address: `localhost:24290` is answered by Y's member
  id, and X (`127.0.0.1:24290`) never got the Put.

`go.mod`/`go.sum` unchanged.

Other pairs tried (`/shared/tmp/b31b/main.go`). Each of these fails the second listen with
`EADDRINUSE`, an error the spec allows:
- `":p"` and `"127.0.0.1:p"`, either order (Go binds `":p"` and `"0.0.0.0:p"` dual-stack, as
  `[::]:p`);
- `"127.0.0.1:p"` and `"0.0.0.0:p"`;
- `"[::]:p"` and `"0.0.0.0:p"`;
- `"0.0.0.0:p"` and `"[::1]:p"`, either order;
- `"[::1]:p"` and `":p"`.

The hostname pair is the one where both listens succeed and a dial is misrouted. Listening on
`"[::1]:p"` first and `"localhost:p"` second gives the same result.

## The Lean side (SKETCH; not built)

A project `netaddralias` (`etc/goose.py`, `local=examples/axiomcx/netaddralias`, modelled on putget's;
`Main` is `Run(zap.NewNop())`).

**The triple of `Run`**, by putget's `Main` proof run twice (`Proof/github_com/mit_pdos/etcd_grove/
examples/etcd/putget/Main.lean:54-200`: `wp_StartServer`, `memberUp_served`, `wp_Serve` with the ghost
step `etcdstart.kv_served` at the address, `wp_NewClient`):
1. Precondition: `memberStartRes "naa-x" {client := "localhost:24290"}` and
   `memberStartRes "naa-y" {client := "[::1]:24290"}` (each `walDirFresh` of the member's WAL
   directory and `netAddrFree` of its client address, `StartRes.lean:70`). Also `etcdstart.bootPremise`
   of each one-member cluster, and putget's package facts.
2. X: `StartServer` (consumes `walDirFresh (memberWalDir "naa-x")` through `bootstrapContract`: a
   fresh member, KV state `σ₀.kvs = []`). Then `Serve x "localhost:24290"`, which consumes
   `netAddrFree "localhost:24290"` in `net.Listen.wp_proof`, gets `netListenerAt l "localhost:24290"`,
   and uses `grpc.start` (in `kv_served`), giving `etcdKVAt "localhost:24290" ... X`.
3. Y: the same at `"[::1]:24290"`.
4. `NewClient "[::1]:24290"` (`plainEndpoint`: no `://`, no `unix:`/`unixs:` prefix, by `decide`). Then
   `cy.Put`, any outcome (`client_Put_own` at Y's `etcdKVAt`; no fact about it is used).
5. `NewClient "localhost:24290"` (`plainEndpoint` by `decide`). Before it, allocate
   `inv kvClientN (∃ σ, etcdKV γX.kv σ ∗ ⌜mvcc.findKey "k0" σ.kvs = none ∧ ...⌝)`, the read-only
   invariant of [wal-tokens](wal-tokens.md)'s step 4 (as putget's `client.putGetInv`, minus the
   flag): no client of X ever writes. `cx.Get` through `grpcInvokerOk` at `["localhost:24290"]` runs
   X's Range handler, so `resp.Kvs = []` and the `if` is dead.

**The closed theorem** `netaddralias_adequate`: as `etcd_putget_adequate`, through
`etcd_adequate_members`, hence `goose_adequacy_start`, with these hypotheses:
- `As := ["localhost:24290", "[::1]:24290"]` and `hAs : As.Nodup`, by `decide`;
- `addrsUnclaimed prog As`: true. No other process binds them (a fresh port), and no unverified code
  of the program binds anything;
- `Ds := [memberWalDir "naa-x", memberWalDir "naa-y"]`, with `Ds.Nodup` and `walDirsAbsent`: true;
- `Hprem`: putget's, for the two clusters.

Conclusion: no thread ends in a panic. Go: the main thread panics.

The step that is false of Go is step 5's: the facts at `"localhost:24290"` describe X, while the
dial of that string reaches Y. The step uses `goose_adequacy_start` (two `netAddrFree`s for two
overlapping strings), `net.Listen.wp_proof` (`netListenerAt` of the string), `grpc.start`
(`grpcServerAt` of the string) and `grpc.ClientConn.Invoke.wp_proof` (`grpcInvokerOk` of the
string). Every other hypothesis is true in the run. `#print axioms` would list the whole server
stack's trust base, as every closed theorem's.

## Which results rest on it

Every closed adequacy theorem takes `goose_adequacy_start` with `addrsUnclaimed`. The list is the same
as [wal-tokens](wal-tokens.md)'s (`grep -rln addrsUnclaimed Proof`: etcdstart's
`Adequacy`/`AdequacyMembers`, `putget`, `putget3`, `partition` (+ `AdequacyWatch`), `cache`,
`compacted`, `compactwatch`, `lease`, `leasecatchup`, `leaseexpiry`, `leasegrant`, `txnlin`,
`watch`, `k8s/compactor`, `k8s/etcd3`). Their own programs do not alias: every address in
`examples/` is a `127.0.0.1:<port>` literal with a distinct port (`grep -rln 'localhost\|\[::'
examples --include=*.go` finds only this counterexample). So their statements stay true of their
programs; what is false is the axiom's general claim, which a new program can instantiate.

## Proposed restatement (not applied)

Make the distinctness a fact of socket addresses. Minimal and checkable: a pure premise on
`net.Listen.spec` (or in `addrsUnclaimed`'s text, with the examples' lists checked by `decide`). Each
address of `As`, and each string `net.Listen` is given with a `netAddrFree`, must be a numeric
`IP:port` literal:
- with no host name (`localhost` resolves through the hosts file or DNS, to several addresses);
- not a wildcard or empty host (`0.0.0.0`, `::`, `""`: dual-stack, overlapping every loopback
  address);
- not an IPv4-mapped IPv6 address;
- with a port in `1..65535` written without leading zeros.

Distinct such strings then name distinct sockets. A dial of a literal reaches only the listener
bound at that literal: Go dials a literal without resolution. A client endpoint `"localhost:p"`
then gets no `grpcServerAt`, because no `Listen` of that string has a spec, so no proof can tie it
to a server.

The same premise covers `httpProtoFree` (`reserve`'s address) and rafthttp's peer hosts. Port `0`
is excluded for a further reason: `Listen("127.0.0.1:0")` binds a random port, and a dial of
`"127.0.0.1:0"` fails. That is an error, not a panic, but `netListenerAt`'s "accepts the
connections dialed to `addr`" is false there too.

## Attacks tried that failed, and why

1. **Two listens of aliases of one socket** (`"127.0.0.1:p"`/`"0.0.0.0:p"`/`":p"`/`"[::]:p"`, and the
   IPv4-mapped form). The second `bind` fails with `EADDRINUSE`, and `Listen.spec`'s post allows an
   error (`Spec/net/Listen.lean:32-33`). The program's `if err != nil { return }` is then live in
   both Go and the proof.
2. **A client of a string nobody listened on** (X at `"127.0.0.1:p"`, a client of `"localhost:p"`).
   Without a listen of that string there is no `grpcServerAt "localhost:p"`, so the client's calls
   have no handler facts and nothing is provable about the reply. The attack needs a successful
   listen of the dialed string, and only the hostname/IPv6 pair gives one.
3. **Leading zeros in the port** (`"127.0.0.1:024290"`): the same socket as `"127.0.0.1:24290"`, so
   attack 1 applies (the second listen fails).
4. **Two `netAddrFree` of one string.** `hAs : As.Nodup` gives one per string, and nothing else
   produces it. `ListenerClose_spec` gives one back, but it is DRAFT and not an axiom
   (`Proof/net/http/ListenerClose.lean`).

### `backend.pathOwn`

5. **Where it comes from.** It is not a start right. `bootOk` gives it (`InvBoot.lean:449`), at the
   string `config.backendPathOf cfg.DataDir`, inside `bootstrapContract`, whose precondition takes
   `wal.bootRes cfg` (the `walDirFresh` of `config.walDirOf cfg.DataDir ""`). The examples fix
   `DedicatedWALDir = ""` (`etcdstart/StartRes.lean:194`). Two `pathOwn`s of one file through
   aliased data directories therefore need two `walDirFresh` of aliased WAL directories: B3-1's gap
   exactly, which adds nothing new. In B3-1's run the fresh member's `bootOk` does give a second
   `pathOwn` of the stopped follower's file, but the follower's (in `srvDiskImage`) is dropped, and
   no snapshot install follows.
6. **Both members live on one backend file** (aliased data directories, or an environment symlink
   `a.etcd/member/snap → b.etcd/member/snap`). The second `bolt.Open` blocks forever on bbolt's
   `flock`:
   - `newBackend` sets `bopts.Timeout = bcfg.Timeout` (`storage/backend/backend.go:231-233`);
   - `OpenBackend`'s config (`server/storage/backend.go:32-60`) never sets `Timeout`;
   - `flock` is per open file description, so an open through a second name in one process blocks.

   This is a hang, not a counterexample.
7. **`os.Rename` onto an aliased `pathOwn`** (a snapshot install while another member holds
   `fileHolds` of the same file). This needs two live backends on the file (attack 6: a hang) or two
   `pathOwn`s (attack 5: B3-1). `rename(2)` onto a symlink replaces the link, not its target, so an
   environment symlink at `member/snap/db` is unlinked by the first install.
8. **A symlink the program creates.** `os.Symlink` has no spec (`Spec/os/` has none), so no proof can
   go through it.
9. **An environment symlink, sequential use** (A runs and stops, then B starts on a path aliasing A's
   backend through a symlink the environment set up). This is the next case.

**Finding (environment, not a refutation): the backend file is not covered by any stated environment
premise.** `walDirsAbsent` says only that no **WAL** is in the directories of `Ds`. `bootstrapContract`
(a premise of every closed theorem, through `etcdstart.bootPremise`) claims a first start's backend
holds no keys (`"%HD"`) and an empty `Meta` (`"%HmEmpty"`, `InvBoot.lean:424-444`). Its comment calls
this "the environment assumption of `HD`/`HDr`", but no hypothesis states it.

Go's `bootstrap` with no WAL opens an existing backend file (`bootstrapBackend`, `beExist`,
`etcdserver/bootstrap.go:255-296`: no check without a WAL) and starts a new cluster over its data.
`TestStaleBackend` (`examples/axiomcx/netaddralias/stalebackend_test.go`) shows it:
- phase 1, in a child process: start a member, put `k0`, stop, then remove `member/wal`. This is the
  environment;
- phase 2, a new process: putget's start and a `Get` of `k0`, which returns `v1`. **10/10** in
  separate processes (`b3-1b-stale10.log`), plus the first run (`b3-1b-stale.log`).

So a closed theorem's hypotheses can all be checked true (`walDirsAbsent` holds: there is no WAL)
while its premise `bootstrapContract` is false of the run. A symlinked `member/snap` (attack 9) is
the same case.

Proposed (not applied): widen `walDirsAbsent` to the member's whole data directory: "no file in
`<name>.etcd` at start, none created there but by the verified code". Equivalently, add a
`dataDirsAbsent` beside it, and use it in `bootstrapContract`'s documented argument.

## Not tried

- `httpProtoFree` / `reserve` to a panic, through rafthttp: a peer URL host `localhost:p` of one
  cluster misrouted to another cluster's member at `[::1]:p`. Expected outcome: a `412` cluster-ID
  mismatch, an error. Two members of one cluster on aliased peer hosts would also change their member
  ids, which are hashed from the URL strings. Not run.
- DNS names other than the hosts file, `127.0.0.2`-style loopback aliases, and IPv6 zones
  (`[fe80::1%lo]`): covered by the proposed literal-address premise.
- A Lean build of the sketch.

## In the Go code

No bug in the verified code: Go's `net` behaves as documented. A `Listen` of a host name binds one
of its addresses, and a dial tries them in RFC 6724 order. etcd's bootstrap over a backend file with
no WAL is a misuse it does not guard against. It is a robustness gap (a member silently starts a
"new" cluster over old data), not filed.
