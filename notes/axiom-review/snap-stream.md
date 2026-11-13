# The snapshot stream: `io.Pipe`, `io.MultiReader`, `snap.Message`, `SaveDBFrom` (axiom sweep B3-3)

Reviewed 2026-11-07 by the `axiom` skill (sweep batch 3, Go first: attacks only, no axiom, spec or
proof changed, no Lean built), in the worktree `/shared/etcd-grove-sweep3` (branch `axiom/sweep-b3`,
at `7c69a7bf63`). Go: go1.27.3 (`io/pipe.go`, `io/multi.go`, `io/io.go`), etcd at the fork pin of
`examples/go.mod` (`upamanyus/etcd/server/v3 v3.0.0-20261103162249-673da07c8fab`; `snap/message.go`
and `snap/db.go` identical to `.lake/go-src/etcd`), `pkg/ioutil/readcloser.go` at the same pin.

## Axioms

| axiom | axiom at | triple at |
|---|---|---|
| `io.Pipe.wp_proof` | `Proof/io/Pipe.lean:41` | `Spec/io/Pipe.lean:33-42` |
| `io.PipeWriter.CloseWithError.wp_proof` | `Proof/io/PipeWriter__CloseWithError.lean:32` | `Spec/io/PipeWriter__CloseWithError.lean:31-36` |
| `io.MultiReader.wp_proof` | `Proof/io/MultiReader.lean:24` | `Spec/io/MultiReader.lean:37-44` (output `http.streamHas`, `Proof/net/http/Boundary.lean:365-383`) |
| `snap.NewMessage.wp_proof` | `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/NewMessage.lean:36` | `Spec/.../api/snap/NewMessage.lean:34-45` |
| `snap.Message.fields.wp_proof` | `Proof/.../api/snap/Message__fields.lean:24` | `Spec/.../api/snap/Message__fields.lean:36-51` |
| `snap.Message.CloseWithError.wp_proof` | `Proof/.../api/snap/Message__CloseWithError.lean:24` | `Spec/.../api/snap/Message__CloseWithError.lean:31-39` |
| `snap.Message.CloseNotify.wp_proof` | `Proof/.../api/snap/Message__CloseNotify.lean:28` | `Spec/.../api/snap/Message__CloseNotify.lean:27-35` |
| `snap.Message.GetTo.wp_proof` | `Proof/.../api/snap/Message__GetTo.lean:30` | `Spec/.../api/snap/Message__GetTo.lean:28-36` |
| `snap.Snapshotter.SaveDBFrom.wp_proof` | `Proof/.../api/snap/Snapshotter__SaveDBFrom.lean:24` | `Spec/.../api/snap/Snapshotter__SaveDBFrom.lean:40-54` |

All are this repository's (Perennial's `io` is names only: no Perennial axiom involved). The other
specs the programs use: `bufferM.ownBuffer_new` (`Proof/bytes/Buffer.lean:44`, an axiom, true: a
zero `bytes.Buffer` is empty), the raft message's `msgOwn_of_struct` (`Proof/go_etcd_io/raft/v3/
InvPbMsg.lean:272`, proved) for `&raftpb.Message{}`, and the writer contract `backend.writerOk`
(a definition, `InvSnapshot.lean:106`) that `io.Pipe` returns for `pw`.

## Verdicts

| axiom | verdict |
|---|---|
| `snap.NewMessage` with `snap.Message.CloseWithError` | **refuted** (Go side; Lean sketched): `NilReader` |
| `snap.NewMessage` with `snap.Message.fields` (`0 ≤ TotalSize`) | **refuted** (Go side; Lean sketched): `NegativeSize` |
| `io.Pipe` + `io.PipeWriter.CloseWithError` (the hand-over `T`), with `snap.NewMessage` + `snap.Message.CloseWithError` (or `fields`' `Close`) | **refuted jointly** (Go side; Lean sketched): `HandOver` gives `False` |
| `io.MultiReader` (its `streamReaderOk` buffer clause), with `snap.Message.fields` (+ `io.Pipe`, `snap.NewMessage`) | **refuted jointly** (Go side; Lean sketched): `Scratch` |
| `snap.Message.CloseNotify`, `snap.Message.GetTo` | **survive** |
| `snap.Snapshotter.SaveDBFrom` | **survives** every attack tried; not reachable standalone (`isSnapshotter` only from `NewServer`), its logger caveat is zap-zero's |

None of the four refutations is reachable from etcd's own code: etcd wraps only the pipe's reader
(`snapshot_merge.go:53`, `newSnapshotReaderCloser`), with a non-negative `dbsnap.Size()`, applies the
pipe's wand before the message exists (`createMergedSnapshotMessage`'s proof), and no reader it
streams overruns its size. They are trust-base bugs (false axioms over a too-general interface),
not Go bugs: no `issues/` or `nonissues/` file.

## The program

`examples/axiomcx/snapstream/snapstream.go` (package `snapstream`), one function per refutation;
`snapstream_test.go` checks that each panics (recovering, printing the value):

```go
func NilReader() {
	m := snap.NewMessage(&raftpb.Message{}, nil, 0)
	m.CloseWithError(nil)
}

func NegativeSize() {
	m := snap.NewMessage(&raftpb.Message{}, nil, -1)
	if m.TotalSize < 0 {
		panic("snap.Message.fields: TotalSize < 0")
	}
}

func HandOver() {
	pr, pw := io.Pipe()
	m := snap.NewMessage(&raftpb.Message{}, pr, 0)
	m.CloseWithError(nil) // closes pr: no readerStreams needed
	var w io.Writer = pw
	w.Write([]byte{1}) // returns 0, io.ErrClosedPipe
	pw.CloseWithError(nil)
	panic("unreachable: CloseWithError handed back T = False")
}

func Scratch() {
	pr, pw := io.Pipe()
	go func() {
		var w io.Writer = pw
		w.Write([]byte{7})
	}()
	m := snap.NewMessage(&raftpb.Message{}, pr, 0)
	var b bytes.Buffer
	mr := io.MultiReader(&b, m.ReadCloser)
	p := make([]byte, 1)
	n, _ := mr.Read(p)
	if n == 0 && p[0] != 0 {
		panic("io.MultiReader: Read wrote past n")
	}
}
```

Runs: `systemd-run --scope -p MemoryMax=32G --quiet go test ./axiomcx/snapstream/ -count=1 -v`
(from `examples/`, `GOTOOLCHAIN=go1.27.3`), **20 separate processes**: 80/80 tests passed, i.e. each
function panicked 20/20 (raw logs `/shared/tmp/7c-logs/b3-3-run{1..20}.log`):

```
NilReader: panic: runtime error: invalid memory address or nil pointer dereference
NegativeSize: panic: snap.Message.fields: TotalSize < 0
HandOver: panic: unreachable: CloseWithError handed back T = False
Scratch: panic: io.MultiReader: Read wrote past n
```

All four are deterministic: `Scratch`'s reader blocks until the writer goroutine's `Write`
(`pipe.go:57-61`), `HandOver`'s `Write` sees `done` closed (`pipe.go:77-79`).

## 1. `NilReader`: `NewMessage` takes any `rc`, `CloseWithError` closes it

**False claim.** `snap.Message.CloseWithError.spec` (pre `msgIs m ml rc` only) says it returns. Go:
`CloseWithError` calls `m.ReadCloser.Close()` (`message.go:58`), the `exactReadCloser` whose `Close`
calls `e.rc.Close()` (`pkg/ioutil/readcloser.go:59`); `NewMessage` stores `rc` as given
(`message.go:44`, `readcloser.go:36-37`) and its spec takes any `rc : GoInterface`, `nil` included.
The same of `fields`' `□ {{True}} rd.Close() {{True}}`, and of any `rc` whose `Close` panics (a
program's own type: `NewMessage` asks nothing of `rc`).

**Lean sketch.** `wp_alloc` the message struct, `msgOwn_of_struct` then `msgOwn_persist` to
`DFrac.discard`; `wp_apply hNM` at `rc := GoInterface.nil`, `sz := 0` gives `msgIs m ml nil`;
`wp_apply hCWE` returns. `{{ isPkgInit snapstream }} NilReader #() {{ RET #(); True }}` from
`snap.NewMessage.spec`, `snap.Message.CloseWithError.spec`.

## 2. `NegativeSize`: `fields`' `0 ≤ TotalSize`

**False claim.** `snap.Message.fields.spec` gives `TotalSize ↦□ tsz ∗ ⌜0 ≤ sint.Z tsz⌝` for every
message `NewMessage` made; its docstring says "`sz` the snapshot's size, not negative", but
`NewMessage.spec` takes any `sz : w64`, and Go sets `TotalSize: int64(proto.Size(rs)) + rcSize`
(`message.go:45`). At `sz = -1` (and also at `sz = 2^63-1` with a non-empty `rs`: overflow) it is
negative.

**Lean sketch.** As 1, then `fields` on `msgIs` gives `TotalSize ↦□ tsz`, `0 ≤ sint.Z tsz`;
`wp_load` reads `tsz`; the `if` on `tsz < 0` is discharged. Axioms: `NewMessage`, `fields`.

## 3. `HandOver`: the pipe's `T` returned without being given up

**False claim.** `io.Pipe.spec` gives the reader's `readerStreams` only for `T` (a wand), and
`io.PipeWriter.CloseWithError.spec` gives `T` back once a `Write` has returned (`c`), on the
argument (`Proof/io/Pipe.lean:32-36`) that "only its holder reads or closes the reader end (no other
code has a contract for it), while a `Write` returns only after a read of its bytes or a close of
the reader end". But two axioms of this repository are such contracts: `NewMessage` accepts the
pipe's reader as `rc` with no resource, and `snap.Message.CloseWithError` (and `fields`' `Close`)
then close it (`message.go:58` → `readcloser.go:59` → `pipe.go:67-73`, `closeRead` closes `done`).
The writer's `Write` then returns `(0, io.ErrClosedPipe)` (`pipe.go:77-79`), `writerOk`'s post makes
`c = true`, and `CloseWithError` hands back a `T` nobody gave up. At `T := False` the rest of the
program is unreachable in the logic; Go reaches the `panic`.

**Lean sketch.** `wp_apply hPipe (Φ := fun _ => True) (T := False)`; keep the wand unused; build
`msgIs m ml (mkOk PipeReader pr)` (`hNM`); `wp_apply hMCWE`; the interface call `w.Write` is
`writerOk`'s triple at `Wr := io.pipeW pw Φ False`, `c := false`, `bs := []`: post `pipeW … true _`;
`wp_apply hPWCWE (err := nil)` (`Φ` trivially holds) gives `if true then False else True`:
`iDestruct` it to `False`. Axioms: `io.Pipe`, `io.PipeWriter.CloseWithError`, `snap.NewMessage`,
`snap.Message.CloseWithError`.

## 4. `Scratch`: `MultiReader`'s reader writes only `n` bytes

**False claim.** `io.MultiReader.spec`'s post `http.streamHas mr Pre Φ'` is transparent: its
`streamReaderOk` (`Boundary.lean:365-373`) says a `Read(p)` returns `ys` with `p ↦* (ys ++ xs.drop
ys.length)`, i.e. `p` unchanged past `n`. That is true of a `bytes.Buffer` and of a pipe's reader
(`pipe.go:59`, `copy`), but `MultiReader` takes any reader with `readerStreams`, and
`snap.Message.fields` hands `rc`'s `readerStreams` to the exact-size wrapper `rd` unchanged
(`readerStreams rc Φ -∗ readerStreams rd Φ`). The wrapper reads into `p` and then, past its size,
returns `0, ErrExpectEOF` (`readcloser.go:47-50`); `multiReader.Read` returns that pair as is
(`multi.go:26-39`: `n > 0 || err != EOF`). So `n = 0` while `p[0]` holds the byte read. Go's own
`io.Reader` contract allows exactly this ("it may use all of p as scratch space during the call",
`io.go:59`), so `streamReaderOk`'s clause is stronger than `io.Reader` itself.

**Lean sketch.** `wp_apply hPipe (Φ := fun _ => True) (T := True)`; apply the wand to get
`readerStreams pr _`; fork the writer (`pipeW`, `writerOk`; its post dropped); `hNM` at `sz := 0`,
`fields` gives `ReadCloser ↦□ rd` and the transfer to `readerStreams rd _`; `ownBuffer_new` for
`b`; `wp_apply hMR` with the slice `[&b, rd]`, `pre := []`; destructure `streamHas` and apply
`streamReaderOk`'s triple at `r := []`, `xs := [0]`: `ys.length = n`, `p ↦* (ys ++ [0].drop n)`;
in the `n = 0` branch `p ↦* [0]`, the load gives `0`, the `panic` is dead. Axioms: `io.Pipe`,
`io.MultiReader`, `snap.NewMessage`, `snap.Message.fields`, plus `bufferM.ownBuffer_new`.

## Reach (by grep; `etc/tcb-report.py --roots` not run: no build)

- `io.Pipe.spec`, `io.PipeWriter.CloseWithError.spec`: `newSnapshotReaderCloser.lean`, the server's
  `Link.lean`.
- `io.MultiReader.spec`: `api/rafthttp/createSnapBody.lean`, `Link.lean`.
- `snap.NewMessage.spec`: `EtcdServer__createMergedSnapshotMessage.lean`, `Link.lean`.
- `snap.Message.CloseWithError.spec`: `rafthttp/snapshotSender__send.lean`,
  `rafthttp/Transport__SendSnapshot.lean`, `Link.lean`.
- `snap.Message.fields.spec`: `snapshotSender__send.lean`, `Transport__SendSnapshot.lean`,
  `createSnapBody.lean`, `Link.lean`.
- The sweep plan's count: 36-39 of 17 exported results (`SaveDBFrom` 12/6).
- `streamReaderOk`'s buffer clause is also what `bodyStream_streamReaderOk` (`Boundary.lean:1015`,
  from `bodyStreamRead_spec`) and `SaveDBFrom`'s pre use: the server-side HTTP body's reader is a
  second place to check the clause (not attacked here: `net/http`'s body readers).

## Proposed restatements (not applied)

1. **A close contract for `rc`** (fixes 1 and 3): `NewMessage` takes `□ rdCloseOk rc`, the
   persistent triple `{{True}} rc.Close() {{err, True}}`, which `fields` and `CloseWithError` then
   use; `io.Pipe`'s wand gives it with the reader's half only: `T -∗ readerStreams pr Φ ∗ □
   rdCloseOk pr`. A message can then wrap the pipe's reader only after `T` was given up, and never
   `nil`.
2. **The size** (fixes 2): `NewMessage` takes `0 ≤ sint.Z sz` and a bound excluding the overflow
   of `proto.Size(ml) + sz` (e.g. `sint.Z sz < 2^62` with the raft message's size below `2^62`,
   or the sum stated with `pbSize`), so every `msgIs` carries a non-negative `TotalSize`; or
   `fields` drops `0 ≤ tsz` and the sender takes it from `NewMessage`'s caller.
3. **Scratch space** (fixes 4): `streamReaderOk`'s buffer post `∃ zs, p ↦* (ys ++ zs) ∗
   ⌜zs.length = xs.length - ys.length⌝` (Go's `io.Reader` rule); a client that needs the tail
   unchanged does not exist (the sender and receiver copy only `n` bytes). Alternatively keep the
   clause and have `fields` not transfer `readerStreams` to the wrapper, but the wrapper is what the
   sender streams.

## What survived, and why

- **`io.Pipe`/`CloseWithError`, `Φ`.** `CloseWithError(nil)` after a partial write: a partial
  `Write` returns only with a non-nil error after the reader's close (`pipe.go:91-92`), and then
  the reader's reads return `ErrClosedPipe`, never `EOF` (`pipe.go:52-53,108-115`): no complete
  stream, `Φ` vacuous. Two `CloseWithError` calls, concurrent writers, a write after the close: all
  need a second `pipeW` (exclusive, consumed). `Write` of an empty slice: sends once
  (`pipe.go:85`), returns `0, nil` after the reader's read (`writerOk`: `k = 0 = chunk.length`).
  A zero-length `Read`: `copy` of 0, no stream change. The reader's stream is every byte of every
  returned `Write`, in order (`wrMu`, `pipe.go:81-82`). The only false part found is `T` (3).
- **`MultiReader`'s `Pre`/`Φ'`.** A nil reader in the list, nested `MultiReader`s (flattening,
  `multi.go:19-25`), `(n > 0, EOF)` readers: the spec fixes the list `[buf, rc]`, `rc` with
  `readerStreams` (only the pipe and the wrapper have one), `buf` exclusive (`ownBuffer`); the
  `EOF` of `buf` is swallowed (`multi.go:33-35`), so `EOF` comes only from `rc`'s, after its
  complete stream. Through the wrapper a short or long stream is an error, never `EOF`
  (`readcloser.go:49-54`; after `ErrExpectEOF` every later read repeats it), so `Φ` holds. The
  input slice is consumed, not returned (weaker, sound).
- **`Message.CloseWithError` twice.** The second send blocks on the full one-slot `closeC`
  (`message.go:46,62-64`) unless someone received (`CloseNotify`'s `isChanBag` at `True`): a block,
  not a panic. A closed `closeC`: the program gets only a `<-chan bool` (`CloseNotify`), which Go
  cannot close.
- **`fields`' `Close` twice or concurrently with a `Read`.** `PipeReader.Close` is idempotent
  (`once`, `pipe.go:72`); the wrapper's `br` race is a data race, no crash. (Its `rc = nil` case is 1.)
- **`CloseNotify`, `GetTo`.** Return a field, and the embedded message's `GetTo` (nil-safe protobuf
  getter; `msgOwn` makes `ml` non-null anyway).
- **`SaveDBFrom`.** A reader that errors midway: `io.Copy` returns the error (`db.go:45,52-54`),
  the spec's success branch is not taken. An empty or short stream: success only at `EOF`, i.e. a
  complete stream (`Φ (r0 ++ t)`). An existing file: kept (`db.go:57-64`), success with no ghost
  step at the rename (as the spec says). `n`: `io.Copy`'s count, never negative. `io.Copy` may use
  `WriterTo` (`*multiReader.WriteTo`, `multi.go:44-69`) instead of `Read`: the same bytes, through
  each reader's `Read` or `bytes.Buffer.WriteTo`. The logger (`db.go:77,85`, `s.lg.Info`): a zero
  `&zap.Logger{}` would panic there, but `isSnapshotter` comes only from `NewServer`'s bootstrap
  (`snap.New(cfg.Logger, …)`, `bootstrap.go:252`; nil becomes `zap.NewNop()`), whose premise
  `cfg.Logger' ≠ null` (`Spec/.../etcdserver/NewServer.lean:172`) is zap-zero's family
  (`notes/axiom-review/zap-zero.md`): the bootstrap logs, and panics, long before, so it adds
  nothing to that finding and is repaired with it. A standalone counterexample needs `isSnapshotter`
  and `snapDirInv`, which no other spec makes.

## Not tried

- The server-side HTTP body reader under `streamReaderOk`'s buffer clause (`bodyStreamRead_spec`):
  `net/http`'s body and chunked readers; the same scratch question as 4.
- `backend.snapshot.WriteTo`'s "at least one `Write` returned" (out of scope: the backend's axiom):
  if bbolt's `Tx.WriteTo` failed before its first `Write`, the goroutine of
  `newSnapshotReaderCloser` would close the snapshot while `createMergedSnapshotMessage` reads its
  `Size()` (`snapshot_merge.go:39,53`).
- The Lean proofs (no `lake build` in this batch) and the closed adequacy form.
