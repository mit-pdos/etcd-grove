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
no tcb collection: the collection `etc/tcb-collections/dsv-hraft.txt` comes with the first `Link`.

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
- **P4** (next): the 185 code-proof files, in four independent groups (`/shared/tmp/ps2/hraft/P4-SPLIT.md`).
  Two lab axioms are to be proved there: `fmt.wp_Errorf_tnErr` (`FmtErrorf.lean`) and `io.Copy`'s.

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
  (`RaftRPC`): a heartbeat (upstream NetworkTransport's test) to raft's heartbeat handler on the
  connection's goroutine, anything else on the consumer channel, then the wait on `RespChan`
  (buffered, so raft never blocks on an abandoned answer). The pipeline is inproc's (one goroutine,
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
