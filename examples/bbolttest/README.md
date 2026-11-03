# bbolttest: the top-level test of bbolt

A program over **real bbolt** (the fork `upamanyus/bbolt`, branch `goose-lean`, pinned by
`etc/goose.py`'s project `bbolt`) whose panics never fire, however often the node crashes, if
bbolt's transactions are **durable** and **strictly serializable**. It is the target of bbolt's
adequacy theorem: the statement to prove is `BootMinibolt`'s (`examples/bboltfs`), for `Boot`.

## The program

`Boot(dir)` is one boot of the node. The database is a bank: four balances and one sequence
number per client, in bucket `bank`.

1. **Recovery** (`recoverState`). It opens the witness file and the database, and checks what the
   database holds:
   - *atomicity*: the balances sum to the initial total, since every transfer moves money all
     or nothing;
   - *durability*: each client's sequence number is at least the largest one the witness says
     was acknowledged, so every transfer whose `Update` returned nil before the crash is there.
   An empty database gets the bank (after checking that the witness acknowledges nothing).
2. **Strict serializability.** Three clients run eight transactions each, concurrently, through
   the lintest driver (`examples/lintest`): transfers (an `Update` that reads two balances and
   the client's sequence number, moves money if the balance covers it, and increments the
   sequence number) and snapshot reads (a `View` of the whole bank). porcupine checks the trace
   against `Model(init)`, the bank's sequential specification from the recovered state. Each
   transaction is one porcupine operation, so a linearizable trace is a strictly serializable
   execution of the transactions.

After a transfer's `Update` returns nil, its client records the new sequence number in the
witness file and makes it durable (`witness.ack`).

**Environmental failures.** Any error from bbolt or the file stops the client (`bank.failed`), the
others then stop too, and `Boot` returns without judging porcupine's answer: a failed commit may or
may not have taken effect, so the trace has no outcome for it. As in `examples/bboltfs`, a
program's claim is about the runs with no environmental failure. `Boot` panics only on a violation.

**The witness file** must survive crashes on its own, under the model's crash relation, where an
unsynced byte may be lost and the unsynced bytes of an extended file are arbitrary (D1 of
`notes/osfs-ext-plan.md`). Per client it has two slots of an 8-byte sequence number guarded by a
flag byte, then an initialization flag after all the slots (as in `examples/crashlog`: zeroed
slots made durable first, so the flag exists only once they are). An acknowledgement clears the
slot's flag, makes that durable, writes the number, makes it durable, then sets the flag and makes
that durable. A set flag therefore always guards an acknowledged number, even when a crash tears a
number being written. Sequence number `s` goes to slot `s % 2`, so the other slot keeps an earlier
acknowledgement meanwhile. The witness's accesses are serialized by a mutex.

**Options.** `bolt.Open(path, 0o600, nil)`: the default options (the array freelist, fsync on
commit, no mlock, the discard logger).

## Go tests

`go test ./...` from this directory (a Go module of its own), also under `-race`:
- `TestBoot`: five boots without crashes; every transfer commits and is acknowledged.
- `TestBootKilled`: boots in a process killed with SIGKILL at arbitrary points, then a last
  boot. A killed process is not a crash of the node (the page cache survives), so this checks
  that no assertion fires when a boot is cut short, not the model's crash relation.
- `TestRecoveryDetectsLoss`, `TestRecoveryDetectsTear`: recovery panics on a witness that
  acknowledges more than the database holds, and on balances that do not add up.
- `TestWitnessFlag`: a torn slot with its flag clear is ignored, and reopening keeps the slots.
- `TestCheckRejectsNonSerializable`: porcupine rejects a bank whose transfer reads and writes in
  separate transactions, so the check has teeth.

## The translation

`etc/goose.py` translates this package (project `bbolttest`) and bbolt with its bodies (project
`bbolt`: the root package, `errors`, `internal/common`, `internal/freelist`) into the parallel tree
`Bbolt/` (modules `Bbolt.Code.go_etcd_io.bbolt`, ...), since the main tree's `go.etcd.io/bbolt` is
the etcd project's names-only translation. Its `os`, `syscall`, `golang.org/x/sys/unix` and
`io/fs` are project bboltfs's (the Linux file extension); `hash/fnv` and `encoding/hex` the main
tree's (names only); lintest and porcupine the main tree's.

## What the proof will need beyond what exists

Standard-library functions bbolt reaches with no body yet: `hash/fnv.New64a` (`Meta.Sum64`),
`os.Getenv` and `strings.ToLower` (`common.Verify`, whose closures call `reflect.DeepEqual` when
`BBOLT_VERIFY` is set), `os.Getpagesize` (`DefaultPageSize`), and `log.New` (the discard logger).
The options avoid the rest: `sort.SliceIsSorted` (the hashmap freelist), `unix.Mlock`
(`Options.Mlock`) and `Tx.WriteTo`'s `io` copies.
