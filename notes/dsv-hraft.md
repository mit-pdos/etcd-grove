# dsv-hraft: hashicorp/raft from dsverify-lab's hraft-4 (#48)

The plan is `/shared/tmp/ps2/hraft/PLAN.md`, agreed on mit-pdos/etcd-grove#48 by coordinator-E
(comment 7225501351). Its stages are:

- S0: the translation;
- S1: the kit over net/rpc;
- S2/S3: the port of the lab's proof;
- S4: the transport;
- S5/S6: the server machine, linearizability and `hraft_nocrash_robust`;
- S7+: crash and restart.

## Status

**S0 (2026-11-27, branch `hraft-s0/2026-11-27`): done.** The fork is in-tree. It is translated into
the part `Dsverify/` by project `dsv-hraft` (`etc/dsv/hraft.py`), and its two packages' initializers
are generated and proved (`etc/gen-init.py`). There is no proof of any function yet, no `Link` and
no tcb collection (P5 added both: `etc/tcb-collections/dsv-hraft.txt`).

The trust added is none:

- no goose `[[skip]]` or names-only entry (there is no `Dsverify/Code/github_com/hashicorp/**.toml`);
- no `TrustedCode`, axiom, `sorry` or `HYP_INITS`.

**S1 (2026-11-27, branch `hraft-s1/2026-11-27`): the kit and the statement, no proof** ("The kit" and
"The statement" below). The trust it adds, for coordinator-E's approval before it lands (#48): the
codec input `examples/hraftnet/rpc.toml` (rpcgen unchanged: its generated codec accepts the kit's types
without a refusal) and the statement's premises (the package-assumption classes and `DistDeploy`); no
goose `[[skip]]` or names-only entry, no `TrustedCode`, axiom, `sorry` or `HYP_INITS`.

**P1-P3 (2026-11-27): the lab's specs and defs ported** ("Port of the lab proof" below); still no proof of a
function, no axiom, `sorry` or premise.

**S4 (2026-11-27, branch `hraft-s4/2026-11-27`): the transport's proof, in progress.** First the two
program changes coordinator-E approved for it (#48 7228496199; "The kit's changes for the transport
proof" below), for the next packet to Upamanyu.
Batch 2: the pure layer (`copyBytes`, `toHeader`/`fromHeader`, the 16 conversions, the size check's 7
bounds), over `Proof/.../hraftnet/rpctransport/Wire.lean`. Batch 3: `Conn` (`NewConn`, `get`, `drop`, `Call`
over Net's `DialTimeout`, `rpc_register`, `NewClient`, `Client.Go`, `Close`, `time.After`;
`rpctransport/Conn.lean`), with kit change 3. Left: the codec laws (the generated codec's encodings and
decodings of the wire structs: stated as `CodecLaws` in `rpctransport/CodecLaws.lean`, round trips over
the pure encodings of `WireEnc.lean`, to prove of the generated codec), the transport's methods and `New`
(over the service spec `raftSvc` of `rpctransport/Facts.lean`: the lab's message facts over wire values),
the receiver
(`RaftRPC`, `deliver`), the pipeline, and the link.

**S5 (2026-11-27, branch `hraft-s5/2026-11-27`): the server machine, the clients, write linearizability,
in progress** ("S5" below). Batch 1: the state machine (`service.Store`) and raft's FSM contract for it,
with the linearization frontier.

## Provenance

| | |
|---|---|
| Go | `examples/dsverify/hraft/` (Go module `github.com/hashicorp/raft`, MPL-2.0 `LICENSE` kept), copied from dsverify-lab `examples/hraft/fork/raft` at lab `c39f136`: the verification fork at commit `02f88d5` (branch `hr-stage4`), on hashicorp/raft v1.8.0 `0f543c0`. The fork's history is the lab's `examples/hraft/history/fork-raft.bundle`. |
| lab proof | dsverify-lab `examples/hraft/proof/` at `241f27e` (tag `final`, Perennial `4c8617a9`), not yet ported |

## Go changes against the lab fork `02f88d5`

1. **The in-process harness is removed:** `examples/{inproc,recorder,kvmodel,hr3}`. Porcupine is dropped
   from `go.mod`, along with its `replace`. `go.mod` gets a provenance comment.
2. **`examples/snapstore/reader.go`: inproc's `Reader`, `NewReader`, `ReadAll` and `copyBytes` move into
   `snapstore`.** `Store.Open` returned `inproc.NewReader(...)`. The code is unchanged apart from the
   package; S1's transport can use `snapstore.ReadAll`/`NewReader`. The lab's proofs of them
   (`examples/inproc/{NewReader,Reader__Read,Reader__Close,ReadAll}.lean`) move to `snapstore`'s
   namespace in the port.
3. **The goose select-send bug (lab D16/D22; mit-pdos/perennial#713).** goose translates a `select`
   send case's value without converting it to the channel's element type (Perennial
   `goose/goose.go:2448`, `ctx.expr(c.Value)`). The fork already converts explicitly at all five such
   sends (`raft.go`'s `case r.fsmMutateCh <- interface{}(...)`, lab D16). Only their comments change:
   they cited the lab's `verify/notes/decisions.md D16` and now cite the goose bug. The lab's other
   instance (D22, `inproc`'s pipeline on a `chan raft.AppendFuture`) went with inproc. S1's
   transport must convert at every select send to an interface-typed channel. The other select sends
   in raft send a value of the element type exactly (checked: `applyCh`, `verifyCh`, ..., the
   `chan bool`/`chan struct{}` notifications).

4. **Two `fmt.Errorf` sites format explicitly** (coordinator-E for Upamanyu, #48 comment 7227641440): error text
   differs; proof-driven; no behaviour change beyond the message. Perennial's `fmt` model is stuck on `%v` of a struct
   or a pointer with no `String()`/`Error()` (`printValue`, which needs reflection).
   - `checkConfiguration` (`configuration.go`): its three messages that showed a `Configuration` or a `Server` under
     `%v` ("empty ID in configuration", "empty address in configuration", "need at least one voter in
     configuration") pass `%s` of the new `formatConfiguration`/`formatServer`, which write `{[{Suffrage ID Address}
     ...]}` and `{Suffrage ID Address}` with `+` and `ServerSuffrage.String()`: the text `%v` wrote, byte for byte.
     Test: `fmtsites_test.go`'s `TestCheckConfigurationMessage` compares each message with `fmt.Sprintf` of the
     original format.
   - `leaderLoop` (`raft.go`): "cannot find replication state for %v" of `id`, a `*ServerID`, printed the pointer's
     address; it is `%s` of `*id` (non-nil there: the line above reads `replState[*id]`), the ID it pointed to. Test:
     `TestLeaderLoopTransferMessage` (a one-server cluster over a stub transport; a transfer to an unknown ID reports
     "cannot find replication state for nosuch"; it fails on the old code with `0x...`).

The fork's other comments citing `verify/notes/decisions.md` (D17 in `replication.go`, D33 in
`api.go`) refer to the lab's `examples/hraft/proof/notes/decisions.md`.

## Translation

- Project `dsv-hraft`: `local=examples/dsverify/hraft`, `root=Dsverify`, lean root
  `github.com/hashicorp/raft=Dsverify`, packages `.` and `./examples/snapstore`, owned
  `github_com/hashicorp`. S1 adds the kit's packages and Net's roots (craq's list).
- Modules:
  - `Dsverify.Code.github_com.hashicorp.raft`, which re-exports `.chunk0`..`.chunk3`;
  - `Dsverify.GeneratedProof.github_com.hashicorp.raft` (`.chunk1`..`.chunk6`);
  - `Dsverify.{Code,GeneratedProof}.github_com.hashicorp.raft.examples.snapstore`.

  The namespace is `Perennial.github_com.hashicorp.raft` (`.examples.snapstore`), as the lab's.
- Diff against the lab's `HrVerify/Code` with `HrVerify` replaced by `Dsverify`:
  - `raft.lean` and chunks 1–3 are identical;
  - `chunk0` differs only where goose now inlines imported constants (`time.Millisecond`/`time.Second`
    become `#(W64 1000000)`/`#(W64 1000000000)`, 9 places: `DefaultConfig`, `ValidateConfig`,
    `snapshotName`). This is BUMP.md's "goose inlines imported constants": the lab proofs that
    `unfold`/`simp` those constants need fixing;
  - `snapstore` differs by the reader move.

## Package facts and initializers

`Dsverify/Proof/github_com/hashicorp/raft{,/examples/snapstore}/Base.lean` hold the facts; the `Init.lean`
files are generated (`etc/gen-init.py`, configured by `etc/dsv/hraft.py`'s `special`), never edited by hand.

- **raft** (since P3): the lab's `pkgGlobals`, statement unchanged: the error variables hold pairwise distinct
  errors, each `errors.newVar` of its message (`errVals`, `isRaftErr`); the three stable-store keys hold
  read-only bytes; `nextObserverID` is in an invariant. Its proof is the lab's `initialize.lean`, moved into
  `hraft.py`'s `raft_cfg` (the generated steps) and `InitLemmas.lean` (its lemmas: `exclS` keeps three quarters
  of each new `errorString`'s field, so the variables' values are distinct, `exclS_nodup`; `wp_New_excl` also
  returns the persistent quarter, which Perennial's `errors.newVar` now holds).
- **snapstore**: the lab's `isInit` (its two `errors.newVar`s, named), from its `errors.New` variables, as craq's.

## Port of the lab proof (S2/S3)

The port is step by step (`/shared/tmp/ps2/hraft/PLAN.md`, section 2; the drift catalogue
`/shared/tmp/ps2/hraft/DRIFT.md`); every ported file starts with its lab path.

- **P1/P2** (`bc8f931ab5`): `proto/`, `gprot/`, `Threads/` (QTok re-proved over leveled thread tokens).
- **P3** (branch `hraft-p3/2026-11-27`): every spec (`Dsverify/Spec/github_com/hashicorp/raft/`, 171 files:
  the lab's but `initialize`; `examples/snapstore/`: 9 of the lab's, and the 5 of the readers that moved from
  inproc, `NewReader`, `Reader.Read`, `Reader.Close`, `ReadAll`, `copyBytes`, now snapstore's) and the defs
  modules (`EncodingLemmas`, `iface/`, `core/`, `leader/`, `handlers/`, `main/`, `DeferRespond`, the top-level
  `*Base`, `Repl*`, `Snap*`). Statements unchanged. Fixes: channel AUs are `|NC=…` now (`iapply
  ncfupd_of_fupd` before an `iinv`), and `lowMask_8`'s `bv_decide` is a kernel proof. The lab's `KitStd.Spec.io.Copy`
  becomes `Spec/io/Copy.lean` in the main tree (no general `io.Copy` spec existed), still to prove over
  Perennial's `io.Copy` body (P4). Not ported (the dropped harness): `inproc` (but its readers), `recorder`,
  `kvmodel`, porcupine, `hr3`, `Goal`, `DsvStatement`.
- **P4** (done): the 185 code-proof files, in four independent groups (`/shared/tmp/ps2/hraft/P4-SPLIT.md`).
  Two lab axioms are to be proved there: `fmt.wp_Errorf_tnErr` (`FmtErrorf.lean`) and `io.Copy`'s.
  - **Group C** (branch `hraft-p4c/2026-11-27`): layers 3-5 (21 files). `Raft__installSnapshot` takes
    `io.Copy.spec` and `io.Copy_Discard.spec` as callee hypotheses, as for raft's own callees (the lab used
    `KitStd.Axiom.io.Copy` directly). **`Spec/io/Copy.lean` is not provable as stated** over Perennial's
    `io.Copy`/`copyBuffer`: (1) a reader of dynamic type `*io.LimitedReader` is not a `WriterTo`, so the spec
    admits it, and then `copyBuffer` loads `l.N`, which `io.streamReader` does not own: the spec needs a
    premise `ts ≠ go.PointerType LimitedReader.ty` (installSnapshot's reader, `*countingReader`, meets it);
    (2) `copyBuffer` compares the reader's error with `io.EOF`, which the model steps only for an error
    whose pointer-typed value is a location (`io.ptrTyped`, as `io.errAt` carries it): `io.streamReader`'s
    `err` needs it; (3) `io.Copy_Discard.spec`'s `w` is any value `Discard` holds: Perennial's `io` fact
    (`io.isInit`, `"#HDiscard"`) says only that `Discard` holds some fixed `Writer`, not `discard{}`, and
    says nothing of `blackHolePool`, which `discard.ReadFrom` takes its buffer from: proving it needs that
    fact strengthened in Perennial (its initializer stores `discard{}`; mechanical). **Settled** (branch
    `hraft-iocopy/2026-11-27`, ledger 2026-11-27): the spec takes (1) and (2) (`io.streamReader`'s post has
    `io.ptrTyped err`; `InstallBase`'s `eof_ptrTyped` gives it for `streamReaderOk`'s `nil`/`io.EOF`), and
    `streamReader`/`streamWriter` are in `streamReaderOk`'s WP form over the resolved call (`methods ty m v`);
    for (3) Perennial `148615524` translates `discard.ReadFrom` and its `io.isInit` gains `"#HDiscardV"`
    (`discard{}`) and `"#HblackHolePool"` (proved). Proved in `Proof/io/Copy.lean`: `io.Copy.wp_proof`, and
    `io.Copy_Discard.wp_proof wp_Get wp_Put` (callees `sync.Pool.Get.spec`/`Put.spec`, Perennial's
    `sync.Pool.wp_Get`/`wp_Put`): P5's `Link.lean` passes these, no axiom.
- **P5** (branch `hraft-p5/2026-11-27`): the Links, `Dsverify/Proof/github_com/hashicorp/raft/Link.lean` and
  `.../raft/examples/snapstore/Link.lean`, generated by dsverify-lab's link generator ported as
  `etc/dsv/tools/hraft-link.py` (modes `etc/gen-link.py --hraft`/`--hraft-snapstore`, so `etc/gates.sh` checks
  them as every generated Link). Every `wp_proof` is applied to its callees' results: raft's and snapstore's
  own, Perennial's (`bytes`, `errors`, `fmt`, `strconv`, `strings`, `sync`, `sync/atomic`, `time` Links) and
  `FmtErrorf`'s theorem for the one `spec_<v>` variant a proof takes (`fmt.wp_Errorf_tnErr`; the generator
  refuses an axiom there). The results are `Perennial.EtcdGrove.raft.<…>.wp_<f>` and
  `Perennial.EtcdGrove.snapstore.<…>.wp_<f>` (`etc/proof_roots.py`: every Link's results are under
  `Perennial.EtcdGrove`; the package's qualifier first, as `etc/verified-code.py` reads a result). Trust base: collection
  `etc/tcb-collections/dsv-hraft.txt` (none of this repository's axioms or `sorry`s). All 188 proofs are linked:
  `Raft.installSnapshot`'s `io.Copy.spec`/`io.Copy_Discard.spec` (`Spec/io/Copy.lean`) by `Proof/io/Copy.lean`
  (branch `hraft-iocopy`), `Copy_Discard`'s over Perennial's `sync.Pool.wp_Get`/`wp_Put`; until then that cone
  (`installSnapshot`, `processRPC`, `runFollower`, `runCandidate`, `leaderLoop`, `runLeader`, `run`, `NewRaft`)
  was left out (the generator's `PENDING`, now empty).

## The kit (S1)

`examples/dsverify/hraft/examples/hraftnet` (Go; translated, packages listed in `etc/dsv/hraft.py`):

- **`rpctransport`**: a `raft.Transport` and `raft.WithPreVote` over net/rpc, generic (no kit constant):
  `New(local, peers, timeout)`. Per peer a `Conn`: one `*rpc.Client` (`net.DialTimeout` and
  `rpc.NewClient`, under the peer's mutex), dropped after a failed or late call so that the next call
  dials again. A call is `Client.Go` into a fresh wire reply and a `select` on its `Done` and
  `time.After`; the reply is converted into raft's response only after it came, so a late reply never
  reaches raft's memory. Wire structs are flat (`Header`, `Entry`, `AppendReq`, ...; rpcgen refuses
  embedded fields, `[]*Log` and `time.Time`; `Log.AppendedAt` is not sent: raft never reads a received
  one). Errors travel as `Failed`/`Err` in the reply; the methods return nil. The receiving side
  (`RaftRPC`): a heartbeat (upstream NetworkTransport's test) to raft's heartbeat handler on a
  goroutine of its own, the connection's waiting for its answer (S4: behavior-preserving), anything else on the consumer channel, then the wait on `RespChan`
  (buffered, so raft never blocks on an abandoned answer). A request whose wire-size bound exceeds `MaxRequest` (1 GiB, the model's frame) is refused with an error and retried by raft (S4: liveness only). The pipeline is inproc's (one goroutine,
  in-order calls; the `raft.AppendFuture(f)` conversion at its select send: mit-pdos/perennial#713).
  InstallSnapshot reads the snapshot (`snapstore.ReadAll`) and sends its bytes in the request; the
  receiver hands raft `snapstore.NewReader` over them.
- **`service`**: the FSM, hr3's one-register `store` (a command is its kind, an 8-byte operation id,
  the value; a command too short to hold the id is a get: the FSM never fails on a command; it is a
  `raft.ConfigurationStore` that ignores the configurations, as hr3's in `Main`), and the API
  (`API`, net/rpc): `Apply` (status done / no effect: `ErrNotLeader`, `ErrEnqueueTimeout`,
  `ErrLeadershipTransferInProgress` / unknown), `Read` (after a `Barrier`; or hr3's way 2: a barrier of
  the current term, `VerifyLeader`, the term unchanged), `AddVoter`, `AddNonvoter`, `DemoteVoter`,
  `RemoveServer`, `LeadershipTransfer` (to raft's pick or a given server), `Snapshot`, `Status`
  (`State`, `LeaderWithID`, `GetConfiguration`'s counts). Each waits for its raft future at most
  `FutureMs` (hr3's `waitFuture`).
- **`hraftnet`**: the machines. `Server(id)`: waits for `n0` from the orchestrator (`awaitConf`, the
  craq/vr pattern), `raftConfig` (hr3's: upstream's test timeouts, `ShutdownOnRemove` off, random
  snapshot threshold, trailing logs and `MaxAppendEntries`), `raft.ValidateConfig` (an invalid one
  returns), in-memory stores and snapstore, `BootstrapCluster` if `id <= n0`, `NewRaft`, the two
  receivers on one `rpc.NewServer` accepting on `ServerAddrs()[id-1]`. `Client(c)`: `remote.ServeClient`
  whose operation tries the servers in turn (`Tries`), a write or a log read through `Apply`, the other
  reads through `Read`; a call sent but unanswered ends the operation unknown, a dial failure or a no-effect
  answer moves to the next server. `Orch()`: picks `n0` (3 or 5), configures, starts `admin`, then
  `remote.Check` of `chooseOps()` operations per client, drawn from 1 to `MaxOps` (`2^20`) as `n0` is
  (porcupine, run to completion; `Model()`: the register with pending writes, `Equal` always false as
  craq's). No workload cap for the checker's speed (Upamanyu, #48 7227997822): the tests pin a small
  number (`kit_test.go`'s `testOps`, HRAFTNET_OPS; `WarmOrch`'s `ops` in the fault runs).
  `admin`: forever, a random request of the six kinds about a random server, at a random server or (one
  time in two) the leader a random server names; hr3's guard of three voters is dropped (no steering:
  one voter is now reachable, the path of fix `0c7aa12`).
- Addresses (`kit_gen.go`, `etc/dsv/kitgen.py`'s `go_consts`): `examples/lib/robust`'s machine addresses,
  server `s` at `10.77.s.1`, client `c` at `10.77.(7+c).1` (the orchestrator, machine 12, listens nowhere),
  so the deployment runs as it is in network namespaces.
- Tests: `kit_test.go`'s `TestDeployment` (the non-vacuity test: runs of the twelve machines in one
  process, each in a network namespace of its own with the addresses on its loopback, `unshare -rn`; over
  the runs every kind of operation answered and every admin request succeeding, `n0` = 3 and 5 both;
  HRAFTNET_RUNS, HRAFTNET_PAR; the admin runs alone HRAFTNET_WARM ms first) and `TestControlStale` (the
  negative control: stale reads are caught); `rpc_gen_test.go` (rpcgen's). `examples/dsverify/hraftrobust`
  (examples module): the twelve machines as processes, one network namespace each, under
  `examples/lib/robust` with its network faults from the start (`covmachine`, tag `covmachine`: a machine
  binary that writes coverage counters, and `WarmOrch`, Orch with the admin alone first).

### Coverage against hr3

Statement coverage of the raft package (2187 statements, `go test -cover`/`covdata`, scripts in
`/shared/tmp/ps2/hraft-s1/tools/`): hr3's `Main` over 100 runs (the lab fork `02f88d5`, whose raft
package is this one's, line for line) against the kit: 40 in-process runs, and the fault runs under
`examples/lib/robust` (221 rounds, partitions one way or both, dropped, and netem link faults, from the start; the admin
alone 8-12 s first). Together: 1459 statements (66.7%) against hr3's 1457 (66.6%).

- hr3 covers 14 blocks (18 statements) the kit's runs did not reach, each in at most a third of hr3's
  runs: schedules of late or lost messages that hr3's adversary made on purpose (inproc's `SlowOut`: a
  leader's calls held up until they arrive in an old term) and the kernel's faults made rarely. They
  are `installSnapshot`'s older-term rejection, its "FSM already past the snapshot" answer (fork
  `db9dde4`) and its kept-log configuration rescan (fork `cc3148d`, 1 run of 100 in hr3),
  `sendLatestSnapshot`'s term check (fork `5894fa2`) and stale-term handling, `replicateTo`'s stop
  after a snapshot and its heartbeat-failure count, a verify future answered by `notifyAll`, a
  configuration change's enqueue timeout, and `max`'s second branch. None is out of the program's
  reach: each is an execution of the theorem's under the net extension's faults.
- The kit reaches 16 blocks hr3 never did, among them hr3's two "in scope, not reached" gaps where the
  lab's last fixes live: `verifyLeader` with a quorum of one (fork `0c7aa12`; hr3 kept three voters) and
  the leadership transfer timing out at the leader (`leaderLoop`, the schedule of fork `02f88d5`);
  also `checkConfiguration`'s "no voter" refusal, a transfer to the leader itself, and a transfer to a
  server not in the configuration.

## The kit's changes for the transport proof (S4)

Three changes to `rpctransport` (the theorem's program), for the next packet to Upamanyu: 1 and 2 approved
by coordinator-E (#48 7228496199), 3 (behavior-preserving) reported on #48 7229406627. The lab's transport contract (`iface/Net.lean`, `isTransport`) was the
in-process transport's; over Net's net/rpc model it met two differences:

1. **The size check (option B).** Net's `Client.Go.spec` asks that the encoded request fit a frame
   (`maxFrameN`, 1 GiB): a longer one is the model's stuck point (`clientCodec.WriteRequest`). rpcgen
   encodes a `[]byte` at 8 bytes per byte, and the contract bounds no request (entries, data, IDs,
   snapshots). The transport now refuses a request whose conservative wire-size bound
   (`AppendReqBound`, `VoteReqBound`, `PreVoteReqBound`, `SnapReqBound`, `TimeoutReqBound` over
   `BytesBound`) exceeds `MaxRequest` (`1 << 30`), with an error (`"rpctransport: request too large"`),
   before sending it. raft retries it as any failed call: **an oversized request is refused and retried,
   a liveness-only cost**; no request of the kit comes near it (commands of at most 9 bytes plus a short
   value, a one-register snapshot). The program checks a fact it can check, so the theorem takes no
   premise. Test: `examples/hraftnet/bound_test.go`'s `TestBounds` (3000 random requests of each kind,
   values and pointers, against the generated encoder `rpcEncode`: the bound is at least the encoding's
   length). Not taken: a size premise in the contract, discharged by raft (option A: above the
   transport), or a model change making an oversized frame an error (option C: trusted, and unfaithful
   to gob, which leaves the stream half-written).
2. **The heartbeat fast path on a fresh goroutine.** The contract's heartbeat handler (`hbHandler`)
   takes the calling thread's quarter token (`rtok`); a net/rpc method runs with none (Net's `callObl`;
   the method goroutine's token is the server's WaitGroup's, `tokJoin.ownDone`). `deliver` now runs the
   handler with `go fn(r)` and waits on `respCh` as before: **behavior-preserving** (upstream's
   NetworkTransport runs it on the connection's goroutine, which waits for the answer either way).

3. **`Conn.Call` reads the received call** (S4 batch 3, reported on #48 7229406627): `case done :=
   <-call.Done: if done.Error != nil`, where S1 read `call.Error` after `case <-call.Done`. Net's
   `Client.Go.spec` gives the call's outcome (its `Error` field, `callPost`) for the value received on
   `Done`, not for the `*Call` `Go` returned; net/rpc sends that same `*Call`, and Go's `rpc.Client.Call`
   reads the received one (`call := <-client.Go(...).Done; return call.Error`). **Behavior-preserving.**
   Diff:

```diff
@@ -377,4 +377,5 @@ func (p *Conn) Call(method string, args any, reply any, d time.Duration) uint64
 	select {
-	case <-call.Done:
-		if call.Error != nil {
+	case done := <-call.Done:
+		// done is call (net/rpc sends the call on its Done), read as rpc.Client.Call does
+		if done.Error != nil {
 			p.drop(c)
```

The diff of changes 1 and 2 (`git diff` of `rpctransport.go`, S1's against S4's batch 1):

```diff
@@ -10,4 +10,5 @@
 // As upstream's NetworkTransport does: a heartbeat (an AppendEntries with a term and a leader and
-// nothing else) goes to the handler raft set (SetHeartbeatHandler), on the receiving connection's
-// goroutine, not through raft's RPC channel; AppendEntriesPipeline is a pipeline whose requests
+// nothing else) goes to the handler raft set (SetHeartbeatHandler), not through raft's RPC
+// channel (upstream runs it on the receiving connection's goroutine; here it runs on a goroutine of
+// its own while the receiving one waits for its answer); AppendEntriesPipeline is a pipeline whose requests
 // are sent one after another and whose answers come back in order; InstallSnapshot carries the
@@ -15,3 +16,5 @@
 // The transport maps a peer's raft address to its network address (New's peers): a raft address
-// need not be a network address.
+// need not be a network address. A request whose encoding may be longer than MaxRequest (the
+// net/rpc model's frame bound; *ReqBound) is refused with an error before it is sent, which raft
+// retries as any failed call: a liveness cost only, which no request of the kit comes near.
 package rpctransport
@@ -142,2 +145,68 @@ type TimeoutResp struct {
 
+// --- the size check
+
+// MaxRequest is the longest encoded request the transport sends: the net/rpc model has no
+// behavior for a request frame longer than 1 GiB (models/net/rpc/codec.go's maxFrame: a client
+// writing one is stuck), so a request whose wire-size bound exceeds it is refused (an error, which
+// raft retries like any failed call: only liveness is lost; no request of the kit comes near it).
+const MaxRequest uint64 = 1 << 30
+
+// tooLarge is the error of a refused request.
+const tooLarge = "rpctransport: request too large"
+
+// BytesBound bounds the encoded length of a byte-slice field (rpcgen's encoding,
+// models/net/rpc/rpcgen_core.py: a sent flag, the length, 8 bytes per byte), saturating above
+// MaxRequest (so that the sums below do not overflow).
+func BytesBound(b []byte) uint64 {
+	n := uint64(len(b))
+	if n > MaxRequest {
+		return MaxRequest + 1
+	}
+	return 17 + 8*n
+}
+
+// hdrBound bounds the encoded length of a Header field (its flag, the struct's, the version's,
+// both slices).
+func hdrBound(h *Header) uint64 {
+	return 16 + BytesBound(h.ID) + BytesBound(h.Addr)
+}
+
+// tagBound bounds the encoded length of a request's type tag and struct marker (the longest
+// tag, rpctransport.TimeoutResp's, has 68 bytes, after its 8-byte length).
+const tagBound uint64 = 128
+
+// AppendReqBound is a conservative bound on the length of the encoding of a (rpcgen's codec):
+// at least it (rpctransport_test.go's TestBounds, against the generated encoder).
+func AppendReqBound(a *AppendReq) uint64 {
+	n := tagBound + hdrBound(&a.Hdr) + BytesBound(a.Leader) + 64
+	for _, e := range a.Entries {
+		if n > MaxRequest {
+			return n
+		}
+		n = n + 64 + BytesBound(e.Data) + BytesBound(e.Extensions)
+	}
+	return n
+}
+
+// VoteReqBound is a conservative bound on the length of the encoding of a (TestBounds).
+func VoteReqBound(a *VoteReq) uint64 {
+	return tagBound + hdrBound(&a.Hdr) + BytesBound(a.Candidate) + 64
+}
+
+// PreVoteReqBound is a conservative bound on the length of the encoding of a (TestBounds).
+func PreVoteReqBound(a *PreVoteReq) uint64 {
+	return tagBound + hdrBound(&a.Hdr) + 64
+}
+
+// SnapReqBound is a conservative bound on the length of the encoding of a (TestBounds).
+func SnapReqBound(a *SnapReq) uint64 {
+	return tagBound + hdrBound(&a.Hdr) + BytesBound(a.Leader) + BytesBound(a.Peers) +
+		BytesBound(a.Configuration) + BytesBound(a.Data) + 128
+}
+
+// TimeoutReqBound is a conservative bound on the length of the encoding of a (TestBounds).
+func TimeoutReqBound(a *TimeoutReq) uint64 {
+	return tagBound + hdrBound(&a.Hdr)
+}
+
 // copyBytes is a fresh copy of b (nil for nil).
@@ -376,3 +445,3 @@ func (t *Transport) DecodePeer(buf []byte) raft.ServerAddress {
 
-// SetHeartbeatHandler sets the handler heartbeats go to, on the receiving connection's goroutine.
+// SetHeartbeatHandler sets the handler heartbeats go to (deliver).
 func (t *Transport) SetHeartbeatHandler(cb func(rpc raft.RPC)) {
@@ -384,4 +453,8 @@ func (t *Transport) SetHeartbeatHandler(cb func(rpc raft.RPC)) {
 func (t *Transport) AppendEntries(id raft.ServerID, target raft.ServerAddress, args *raft.AppendEntriesRequest, resp *raft.AppendEntriesResponse) error {
+	w := toAppendReq(args)
+	if AppendReqBound(w) > MaxRequest {
+		return errors.New(tooLarge)
+	}
 	reply := new(AppendResp)
-	if err := t.send(target, "AppendEntries", toAppendReq(args), reply); err != nil {
+	if err := t.send(target, "AppendEntries", w, reply); err != nil {
 		return err
@@ -396,4 +469,8 @@ func (t *Transport) AppendEntries(id raft.ServerID, target raft.ServerAddress, a
 func (t *Transport) RequestVote(id raft.ServerID, target raft.ServerAddress, args *raft.RequestVoteRequest, resp *raft.RequestVoteResponse) error {
+	w := toVoteReq(args)
+	if VoteReqBound(w) > MaxRequest {
+		return errors.New(tooLarge)
+	}
 	reply := new(VoteResp)
-	if err := t.send(target, "RequestVote", toVoteReq(args), reply); err != nil {
+	if err := t.send(target, "RequestVote", w, reply); err != nil {
 		return err
@@ -408,4 +485,8 @@ func (t *Transport) RequestVote(id raft.ServerID, target raft.ServerAddress, arg
 func (t *Transport) RequestPreVote(id raft.ServerID, target raft.ServerAddress, args *raft.RequestPreVoteRequest, resp *raft.RequestPreVoteResponse) error {
+	w := toPreVoteReq(args)
+	if PreVoteReqBound(w) > MaxRequest {
+		return errors.New(tooLarge)
+	}
 	reply := new(PreVoteResp)
-	if err := t.send(target, "RequestPreVote", toPreVoteReq(args), reply); err != nil {
+	if err := t.send(target, "RequestPreVote", w, reply); err != nil {
 		return err
@@ -425,4 +506,8 @@ func (t *Transport) InstallSnapshot(id raft.ServerID, target raft.ServerAddress,
 	}
+	w := toSnapReq(args, b)
+	if SnapReqBound(w) > MaxRequest {
+		return errors.New(tooLarge)
+	}
 	reply := new(SnapResp)
-	if err := t.send(target, "InstallSnapshot", toSnapReq(args, b), reply); err != nil {
+	if err := t.send(target, "InstallSnapshot", w, reply); err != nil {
 		return err
@@ -437,4 +522,8 @@ func (t *Transport) InstallSnapshot(id raft.ServerID, target raft.ServerAddress,
 func (t *Transport) TimeoutNow(id raft.ServerID, target raft.ServerAddress, args *raft.TimeoutNowRequest, resp *raft.TimeoutNowResponse) error {
+	w := &TimeoutReq{Hdr: toHeader(args.RPCHeader)}
+	if TimeoutReqBound(w) > MaxRequest {
+		return errors.New(tooLarge)
+	}
 	reply := new(TimeoutResp)
-	if err := t.send(target, "TimeoutNow", &TimeoutReq{Hdr: toHeader(args.RPCHeader)}, reply); err != nil {
+	if err := t.send(target, "TimeoutNow", w, reply); err != nil {
 		return err
@@ -568,4 +657,7 @@ func isHeartbeat(a *raft.AppendEntriesRequest) bool {
 // deliver hands raft cmd (with data, InstallSnapshot's reader; nil otherwise): a heartbeat (hb)
-// to the heartbeat handler if raft set one, on this goroutine, anything else to the consumer;
-// then it waits for raft's response.
+// to the heartbeat handler if raft set one, on a goroutine of its own, anything else to the
+// consumer; then it waits for raft's response. (Upstream's NetworkTransport runs the handler on
+// the connection's goroutine; here the RPC's goroutine waits on respCh while it runs, which is the
+// same behavior: the fresh goroutine is what gives the handler a thread of its own in the proof,
+// since net/rpc's method goroutine lends none.)
 func (t *Transport) deliver(cmd any, data io.Reader, hb bool) (any, error) {
@@ -580,3 +672,3 @@ func (t *Transport) deliver(cmd any, data io.Reader, hb bool) (any, error) {
 	if fn != nil {
-		fn(r)
+		go fn(r)
 	} else {
```

## The statement (S1)

`Dsverify/Spec/github_com/hashicorp/raft/examples/hraftnet/TopLevelRobustness.lean`,
`hraft_nocrash_robust.spec` (hand-written: kitgen's statement quantifies the thread bound), over
kitgen's `TopLevelDefs.lean` (`system`, `hraftKitAddrs`, `hraftStepBound := 2 ^ 62`,
`hraftThreadBound := 2 ^ 28`) and `Addrs.lean`. No proof file yet. Premises, classified (the robustness
skill's checklist): `cmd.*.Assumptions` and `go.BasicIntoValInj` (package assumptions of the
translations, trusted); `DistDeploy hraftKitAddrs (system σ) g` (start state and environment: the
addresses distinct and valid, no connection, no listener; Net's audited definition); nothing else (the
configuration is chosen and validated in Go). The bounds are the lab proof's (hraft-4: `ReceiptBoundLe
(2 ^ 62)`, D2; D15's quarter thread tokens); the port either keeps them or states higher ones.


## Deviations from upstream v1.8.0

The fork's commits on v1.8.0 `0f543c0` (dsverify-lab `examples/hraft/history/fork-raft.bundle`, branch
`hr-stage4`), less the lab's `examples/` commits (S0 removed them). Upstream `main` (`dd4346d`,
2026-11-23) has the same Go code as v1.8.0 (copyright lines only). Each fix's test fails at both and
passes on the fork; the lab's issue tests are run with `issues/hraft-harness/run.sh` (the five of
hraft-4 are this repository's `issues/hraft-*`; nine earlier ones are dsverify-lab's
`examples/hraft/proof/issues/<slug>/`, run the same way, 2026-11-27: 3 of 3 fail at `main`, 3 of 3 pass
on the fork; `39e0c82`'s is upstream's hashicorp/raft#733, reproduced there).

| commit | change | reason | test |
|---|---|---|---|
| `5faf1a9` | the raft package only (no net/TCP transports, file snapshot store, peers.json, test helpers, `InmemTransport`); hclog and go-metrics statements removed (an AST pass), with the variables, config fields and parameters only they used, and the saturation metric (floating point); MsgPack replaced by a hand-written `Configuration` encoding (`encoding.go`); `crypto/rand`, `math/rand` by `primitive.RandomUint64`; `container/list` (`leaderState.inflight`) by a slice; `sort.Sort` of the match indexes by an insertion sort; `replicate`'s and `replicateTo`'s gotos and two labeled breaks by loops with flags | Goose and Perennial: no model of hclog, go-metrics, msgpack, `container/list`, `sort.Sort` over an interface; no goto or label | none (no behavior change intended; the goto rewrite is the one that touches control flow) |
| `39e0c82` | `appendEntries` commits only up to the index the request vouches for | upstream hashicorp/raft#733 (PR #734) | #733's (lab `follower-overcommit`, not rerun) |
| `004dfaa` | `replicateTo` does not send an AppendEntries built across a change of term | state-machine safety | lab `deposed-leader-mixed-append` |
| `f97e955` | explicit `interface{}` conversions at the select sends on `fsmMutateCh` | goose's select-send bug, mit-pdos/perennial#713 (no behavior change) | none |
| `a1d5582` | `appendStats` takes the entry count as an `int` | the stripped metric's leftover (no behavior change) | none |
| `ae71703` | the heartbeat fast path changes neither the term nor the state | upstream hashicorp/raft#695 | lab `heartbeat-fastpath-race` |
| `4dd03b4` | `pipelineSend` does not send an AppendEntries built across a change of term | state-machine safety | lab `pipeline-mixed-append` |
| `d660d8b` | `verifyLeader` counts only responses to heartbeats sent after the verify was registered | linearizability of `VerifyLeader` reads | lab `verify-stale-vote` |
| `ea6e596` | `VerifyLeader` answers once the FSM has applied every entry committed before it | linearizability of `VerifyLeader` reads (Raft's read-only queries, step 4) | lab `verify-read-fsm-lag` |
| `5c0b97e` | `installSnapshot` discards the log unless it holds the snapshot's last entry | upstream hashicorp/raft#721 (Fig. 13 steps 6-7) | lab `snapshot-install-conflict` |
| `db9dde4` | `installSnapshot` does not restore a snapshot the FSM has applied past | linearizability (the FSM went back) | lab `snapshot-rollback` |
| `4daeb61` | `sendLatestSnapshot` does not answer verify futures with an InstallSnapshot's response | linearizability of `VerifyLeader` reads | lab `snapshot-stale-vote` |
| `5894fa2` | `sendLatestSnapshot` does not send a snapshot after the term changed | state-machine safety | lab `deposed-leader-snapshot` |
| `9f26652` | `latestConfiguration` is an `atomic.Pointer[Configuration]` | Perennial's `atomic.Value` (no behavior change) | none |
| `6c3454c` | `verifyLeader` counts only the latest configuration's voters' responses | upstream hashicorp/raft#725 (PR #740) | `issues/hraft-verifyleader-nonvoter-vote` |
| `4bb3955` | the leader's own vote counts only if it is a voter of its latest configuration | linearizability of `VerifyLeader` reads | `issues/hraft-verifyleader-removed-leader-self-vote` |
| `0c7aa12` | with a quorum of one, `VerifyLeader` answers once the FSM has applied every committed entry | `ea6e596`'s wait on the one-voter path | `issues/hraft-verifyleader-single-voter-fsm-lag` |
| `cc3148d` | `installSnapshot`, keeping the log, takes the latest configuration from the entries after the snapshot | state-machine safety | `issues/hraft-installsnapshot-drops-newer-configuration` |
| `02f88d5` | `runCandidate` counts the election's votes against the latest configuration's quorum, after the pre-vote | election safety | `issues/hraft-candidate-stale-quorum` |

In-tree after S1 (branch `hraft-fmtsites/2026-11-27`, P4; coordinator-E #48 7227641440, Upamanyu's
standing decision of 2026-11-24): two `fmt.Errorf` call sites rewritten to format explicitly, since
Perennial's `fmt` model does not format `%v` of a struct or a pointer (`printValue` needs reflection):
`checkConfiguration`'s message on a configuration (its servers' suffrage, ID and address written
field by field) and `leaderLoop`'s on a `*ServerID` (dereferenced, `%s`, nil guarded). Error text
differs; proof-driven; no behavior change beyond the message; each with a test that the message still
names the same values.

In-tree since (S0): inproc's `Reader`, `NewReader`, `ReadAll`, `copyBytes` moved into
`examples/snapstore/reader.go`; the conversions' comments cite mit-pdos/perennial#713.

## S5

### The state machine (batch 1)

`service.Store` is proved over the real code (`Dsverify/{Spec,Proof}/github_com/hashicorp/raft/examples/hraftnet/
service/`: `NewStore`, `encodeState`, `Store.Apply`, `Store.StoreConfiguration`, `Store.Snapshot`, `Store.Restore`,
`snapshot.Persist`, `snapshot.Release`), and `FsmIface.lean` derives raft's FSM contract (`iface/FSM.lean`'s
`isFSM`, `fsmNotBatching`) from their specs, as the lab's hr3 `ServerFSM.lean`. The vocabulary
(`FsmDefs.lean`) is hr3's (`ServerDefs.lean`): the register after a committed prefix (`regOf`), the answer to
its last command (`respAt`), the store's mutex invariant (`storeInv`), the snapshot's bytes (`snapBytes`),
`respP`/`snapP` (raft's `RCtx` fields), with the kit's command format (a put is `P`, an 8-byte id, the value;
anything else is a get) and Perennial's `strconv.Itoa` (`fmtInt`) for the snapshot's index.

**The linearization frontier.** hr3 linearized offline (`LinPure`, over the committed prefixes every response
carried). remote's clients need online linearization points (`remote.lin`, an atomic update the far side
fires once). The commit step is gprot's (`commit_upd`, in `leaderLoop`), so firing there would change the
lab's protocol invariant; the FSMs fire instead. `frInv γ fc` keeps the **frontier**: the longest committed
prefix any server's FSM has applied, ending with a command, with the clients' state at it (`fc.Q es`, the
clients' choice). An FSM that applies the command right after the frontier moves it, and moves the clients'
state by their law `linStep` (`Q es ={⊤ \ frN}=∗ Q (es ++ ns ++ [e])`: there the clients fire the update of
`e`'s operation, helping); an FSM behind the frontier applies the same entries and moves nothing
(`frontier_apply`: the frontier cannot stop between the FSM's prefix and its next command, which is the
only command there). Every response and snapshot carries `frLb` of its prefix: a client whose `Apply`
answered `nil` finds its operation already linearized, its output the FSM's answer. The first application
of an index is monotone in the index (an FSM applies in order), and it lies between the operation's call
(the command is appended after it) and its return (the leader's FSM answers the future), so it is a valid
linearization point. Reads outside the log (S6) read some FSM's state, which may be behind the frontier:
they need the frontier at their call (the barrier's bound) instead.

`Store.Restore` takes `strconv.Atoi_dec.spec` (`Spec/strconv/Atoi_dec.lean`: `Atoi` of `Itoa(n)`, `n ≥ 0`,
returns `(n, nil)`) as a callee hypothesis: true of Go, but Perennial's `Atoi` spec does not give the number
(`notes/perennial-changes.md`). Not an axiom; to be proved over Perennial's `Atoi` (or in Perennial).

Still to do in S5: the API service's methods over raft's API specs (`waitFuture`, `Apply`, the admin
requests, `LeadershipTransfer`, `Snapshot`, `Status`; `Read` with S6), the server machine (`Server`:
configuration, the stores, `BootstrapCluster`, `NewRaft`, the receivers), the clients' operation (`Sys.op`
over `Conn.Call` into the API, the clients' state `Q`: the model's state half, the operations' updates in an
escrow keyed by the command's datum, gprot's `opsAuth`, and `linStep`'s proof), the orchestrator and the
admin, and the link.
