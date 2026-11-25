# kvraft: kvdurable over a real network, with real crashes (2026-11-15)

**Status:** test only, not translated, not verified. Its statement is stated (2026-11-15, branch
`robustness`): `kvraftRobust`, over the Lean library `Robustness` (`notes/robustness.md`). The proof waits
for a network semantics (the user's, branch `net-tcp`) and an adequacy theorem for `Robustness.Run`.
Branch `kvraft`; its test now runs over the harness `examples/lib/robust` (branch `robustness`).

## What it is

`examples/raft/kvraft` is `examples/raft/kvdurable` with every replica a process of its own, talking to
its peers and clients over `net.Conn` (TCP on the loopback interface). The store, the durable file
(`durable.Write` of the replica's storage image), every durability choice, the snapshot goroutine, the
reconfigurations and disruptions are kvdurable's, unchanged where they could be:

- `storage.go`: kvdurable's, unchanged but the package name. `codec.go`: kvdurable's encodings and
  `validConf`, unchanged.
- `replica.go`: kvdurable's `Replica` without `stop`/`crash`/`crashed` (a process is an incarnation:
  it ends by being killed or losing power), and with the read sequence numbers given by the clients
  (kvdurable's cluster-wide `readSeqs` becomes the clients' duty: they never reuse one).
- `wire.go`, `transport.go`: frames (8-byte length, body) and the messages encoded by hand (`putMsg`/`getMsg`,
  over storage.go's `putEntry`/`putSnapshot`: no `proto.Marshal`, as kvdurable's `copyMsg`); one TCP
  connection per peer, dialed when needed; a message that cannot be written is dropped and reported
  (`ReportUnreachable`, `ReportSnapshot`), never retried. (Until 2026-11-15 the transport also dropped,
  delayed, duplicated and cut at random, `Faults`; gone: every network fault is now the environment's,
  made by the kernel in the harness's router namespace, `notes/robustness.md`.)
- `node.go`, `client.go`: the process (`RunNode`: listen, start from the file as kvdurable's
  `Cluster.start`, serve), and the client protocol (one request frame, one response frame per connection:
  propose, read, conf change, disrupt, status).

## The test (`driver`, `cmd/kvraft`)

`go run ./raft/kvraft/cmd/kvraft check -rounds N [-crash kill|power|mixed]` (from `examples/`); `go test
./raft/kvraft/...` (kill mode; `KVRAFT_POWER=1` adds the power-loss round, which needs sudo).

- Up to 9 replica processes; 4 clients of 100 random Put/Get/Read, one to three proposers of random
  configuration changes (new replicas started as processes), leadership disruptions.
- **Crashes are real.** A replica's process is SIGKILLed at a random time, then either:
  - *kill*: its filesystem is synced (`sync -f`) before it restarts, the restart `fsExt`'s "Restarts"
    assumption allows (`notes/decisions.md`, "One file semantics, fsExt; power loss only");
  - *power*: its machine's disk loses power. Every replica has an ext4 of its own (configuration C:
    `mkfs.ext4` defaults on a 1 GiB sparse image, default mount) on a dm-flakey device over a loop
    device; a power loss is xfstests' `_flakey_drop_and_remount`: `dmsetup suspend --nolockfs`, the table
    switched to `drop_writes`, unmount (the dirty pages and last journal commits are dropped), the table
    switched back, mount (journal replay). `driver.TestPowerLoss` checks the mechanism: an unsynced file
    and an unsynced overwrite are lost, fsynced data and `durable.Write`'s file survive.
- Porcupine checks the trace; the members must converge; then **the whole cluster crashes at once**
  (in the round's crash mode), restarts, must converge again on the same contents, and a Read of every key
  must return what the store held.
- A replica process that exits on its own (a panic of raft's or the store's) fails the run, with its log.

## Results (2026-11-15)

- Kill rounds and power rounds pass; e.g. 58 power losses in a round, 116 kills in another; the race
  detector (the replicas are the race-built test binary) is clean.
- Mutation check: `persist` with `os.WriteFile` (no fsync, no rename) passes kill mode and fails power
  mode (the final power loss leaves the store empty: "applied 319 ... after, applied 0").
- Single-replica power losses mid-run did not expose that mutant on their own in the run tried (the
  final whole-cluster crash did): a weaker durability bug may need more rounds, or the final crash.

## Review (2026-11-15)

A code review of the branch found no protocol-level bug in the replica (wire format, transport, run loop,
durability). Fixed in the driver and node: a crash could pick a replica the driver had listed before its
process existed (nil panic in the driver); the incarnation count was read without the lock; the replicas'
addresses were on 127.0.0.1, where a connection's source port could take a down replica's port (now one
random 127.a.b.c per run: connections' source address is 127.0.0.1, checked); the counters' read before a
kill could wait 0.5 s (`RequestWithin`); `Accept` errors spun; small simplifications (`Replica.contents`
copies the map, no sender for the node's own id, `Replica.conf` removed). Kept: `model.go` copies
kvdurable's model, like `storage.go` and `codec.go`, so the package stands alone.

A stress round then failed the convergence check on raft's liveness, not the store's: with PreVote and
CheckQuorum off, a learner that adopted a removed voter's higher term ignores the leader for good
(`nonissues/raft-learner-stranded-higher-term.md`). The check now lets such a learner lag in that option
combination, and reports it (`stranded learners`).

## For the proof

- Network operations used: `net.Listen`, `Listener.Accept`, `net.DialTimeout`, `Conn.Read`, `Conn.Write`,
  `Conn.SetDeadline`/`SetReadDeadline`/`SetWriteDeadline`, `Conn.Close`. Nothing else (no `bufio`, no
  `io.ReadFull`: `readFull`/`writeAll` loop on `Read`/`Write`).
- Files: `durable.Read`/`durable.Write` (to be reimplemented over `os` and proved over `fsExt`, per the
  decision above).
- The statement to aim for: the replica program, run as any number of processes under power losses, with
  any clients that never reuse an operation id or read sequence number, is linearizable (the driver is the
  test's harness: it is not the verified program). kvdurable's proof is the template for everything below
  the transport.
- Not Goose-checked yet: `stats.go` uses an array of atomics, `args.go` the `flag` package (the latter
  is only the process's command line; the proof would start from `StartNode`/`RunNode` with a
  `NodeConfig`).

## Over the robustness harness (2026-11-15, branch `robustness`)

The driver runs every replica on a machine of its own of `examples/lib/robust` (a network namespace;
one loopback address without root), clients' operations from four client machines, and, in the
namespace mode, `robust.NetNemesis`: partitions (both ways or one way, drops or resets, a machine
isolated) and netem link faults (delay, jitter, loss, duplication, reordering), concurrently with the
crashes. `cmd/kvraft check` re-runs itself as root (`sudo -n`) for it; `KVRAFT_NETNS=1 go test
./raft/kvraft/driver -run TestNetns`. Ten rounds: porcupine `Ok` and convergence in each
(`notes/robustness.md`, "Results").
