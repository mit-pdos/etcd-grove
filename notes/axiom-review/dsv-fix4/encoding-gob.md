# Axiom review: `encoding/gob` for SwiftPaxos's `MSync` (dsv-fix4)

Reviewed 2026-11-25 by the `axiom` skill (an independent reviewer), in the worktree
`/shared/etcd-grove-mathrand` (branch `dsv-fix4`, at `ae48f8d845` plus the uncommitted files that
add these axioms); Go's `encoding/gob` at the pinned toolchain go1.27.3
(`~/go/pkg/mod/golang.org/toolchain@v0.0.1-go1.27.3.linux-amd64/src/encoding/gob`, identical to
`/usr/local/go/src/encoding/gob`).

## The axioms

Pure vocabulary and laws (`Dsverify/Proof/encoding/gob/Vocab.lean`): the opaque predicates
`wireBytes : SyncWire → List w8 → Prop` and `wireFits : SyncWire → Prop`; the opaque tokens
`encoderTok`, `decoderTok` (no laws); and the axioms, each a field of `sp.GobFmt`
(`Dsverify/Spec/github_com/imdea_software/swiftpaxos/swift/Wire.lean`), word for word:

    wireBytes_peel   : wireBytes a ba → wireBytes b bb → ba ++ x = bb ++ y → a = b ∧ ba = bb
    wireFits_of      : m.cEnc.length < 2 ^ 31 → wireFits m
    wireBytes_exists : KitVal.wf (.msync m) → wireFits m →
                         ∃ m' bs, KitVal.equiv (.msync m) (.msync m') ∧ wireBytes m' bs

Hoare-triple axioms (`Dsverify/Proof/encoding/gob/{NewEncoder,NewDecoder,Encoder__EncodeW,
Decoder__Decode}.lean`), each `letI := swiftLibsOf π; encoding.gob.X.spec`, the specs in
`Dsverify/Spec/encoding/gob/` over `Defs.lean`:

- `NewEncoder.spec`: for every `w`, `NewEncoder(w)` returns `enc` with `ownEncoder enc w`
  (= `encoderTok`).
- `NewDecoder.spec`: `NewDecoder(r)`, `r` a `*bufio.Reader`, returns `dec` with
  `ownDecoder dec r` (= `decoderTok`).
- `Encoder.EncodeW.spec`: with every reordering of `m` fitting, given `writeSink e S Q`,
  `prefixClosed Q`, `ownEncoder enc (ok e)` (consumed), `S W`, `syncOwn l dq m`, and `□ Q (W ++ bs)`
  for every candidate stream `bs` of a reordering `m'`: `enc.Encode(l)` returns some `err` and
  gives `∃ m' bs, equiv m m' ∧ wireBytes m' bs`, `syncOwn l dq m` and `S (W ++ bs)`, **whatever
  `err` is**.
- `Decoder.Decode.spec`: given `readsOk rd I`, `I R`, `ownDecoder dec rd` (consumed) and
  `l ↦ zero MSync`, `dec.Decode(l)` returns `e` and `∃ data, I (R ++ data)`, and if `e = nil`,
  `∃ m'` with `syncOwn l 1 m'` and the pure fact: every `wireBytes m bs` with `data ++ u = bs ++ w`
  has `data = bs` and `equiv m m'`.

Claims, in plain words: (1) gob's stream of one `*MSync` from a fresh encoder is self-delimiting,
prefix-free among such streams, and determines the value including its maps' listing order;
(2) a value whose lab-codec measure is under 2^31 bytes is under gob's message limit; (3) every
such value is encodable; (4) `NewEncoder`/`NewDecoder` never panic; (5) `Encode` of an `*MSync`
never panics, errs only through `Write` or the size limit, and writes (in pieces) a stream of
some listing of the value; (6) `Decode` on a fresh decoder over a `*bufio.Reader` never panics,
for **any** input bytes, reads only through `Read`, and on success has read exactly one stream
and filled `*v` with its value; (7) each encoder/decoder is used once (token consumed).

Used by: `(*MSync).Marshal`/`Unmarshal` (`examples/dsverify/swiftpaxos/swift/defs.go:417-428`),
proved in `Dsverify/Proof/github_com/imdea_software/swiftpaxos/swift/MarshalSync.lean` and
`TableSync.lean` (`MSync.Unmarshal.wp_proof`); the laws through `sp.GobFmt` (`NewLeaderAckNs.lean`,
`SyncFits.lean`, the `RecSync*` files).

## Verdict: **survives with conditions**

No counterexample program was found. Conditions (C1-C3 below): one docstring claim about
`Encode` is false (it does not stop at the first failed `Write`), which the spec's `writeSink`
tolerates but does not justify the post `S (W ++ bs)` in that case; and the generic names-only
context condition.
`Decode`'s no-panic claim for arbitrary input bytes rests on fuzzing, not a proof (C2).

## Attacks tried

1. **Two different `MSync` values with comparable streams (`peel`).** Gob writes each message as
   its length (gob unsigned: one byte below 128, otherwise a byte `-count` then `count` big-endian
   bytes, `encoder.go:64-82`), so message headers are prefix-free and two streams read from the same
   start split into the same message boundaries until they differ. A fresh encoder writes the type
   definitions (`sendTypeDescriptor`, `encoder.go:160-185`; each message starts with a negative id,
   `sendActualType` line 102) and then exactly one value message (positive id, `sendTypeId` +
   `writeMessage`, `encoder.go:241-247`). So if one stream is a prefix of the other, the shorter's
   value message is a message of the longer at a non-final position, which has a negative id:
   contradiction unless equal. The bytes determine the value: `int32`/`int`/`int64`/`uint8` are
   lossless, a nil map is not sent and a non-nil empty one is (`encode.go:532-538`, so
   `none`/`some []` differ), entries are written in `MapRange` order (`encode.go:365-376`) so the
   listing is in the bytes. The model's only identifications (nil vs empty `Value`, nil vs empty
   `Dep`, both `[]` in Lean) make the bytes equal or different but never break `a = b`: two
   encodings of one `SyncWire` are each full streams, and prefix-comparable full streams are equal.
   Type ids differ between processes (assigned at first use), but `peel` only needs the decoding of
   a byte string to be a function. Tested: three values (nil maps, an empty map, negative ids,
   `Op = 255`, nil/empty `V` and `Dep`) round-trip with the nil/empty map distinction kept.
2. **A stream that is not self-delimiting / a decoder that reads past it.** `NewDecoder` keeps an
   `io.ByteReader` as is (`decoder.go:47-50`); the decoder reads each count with `io.ReadFull` of
   1 then up to 8 bytes (`decodeUintReader`, `decode.go:114-142`) and each body with
   `saferio.ReadData` (`io.ReadFull` in chunks), only through `Read`, the method `readsOk` covers.
   `decodeTypeSequence` reads a new message only when the buffer is empty and returns at the first
   id ≥ 0 (`decoder.go`), so a successful `Decode` has read exactly the type definitions and the
   first value message. Tested: each encoded stream followed by 4 garbage bytes, decoded through a
   `*bufio.Reader`: exactly `len(bs)` bytes consumed, the 4 left.
3. **`fits_of` (the 2^31 measure against `tooBig = 1 << 33`).** Per item gob takes at most: a
   `CommandId` 13 bytes (two fields of delta 1 + zig-zag `int32` ≤ 5 bytes, end 1) against 16;
   a phase entry 22 against 24; a command entry `37 + |V|` against `40 + |V|` (`Op` up to 2 bytes
   since 255 ≥ 128); a dependency entry `22 + 13n` against `24 + 16n`; a map's delta and count ≤ 10
   against 9; the top-level type id and struct end a few bytes. So the value message is at most the
   measure plus a constant, far under 2^33. The only other `Encode` errors for this type
   (`errorf` sites, `encode.go`: nil elements, interfaces, no exported fields, unaddressable) cannot
   arise: `MSync` has no pointers or interfaces and every struct has exported fields.
4. **`exists_bytes`.** Every `SyncWire` with distinct keys is the listing of some Go `MSync` (all
   field ranges are bijective with the Go types on 64-bit), and `Encode` with succeeding `Write`s
   writes a stream of it in `MapRange` order: true.
5. **Encode panics.** The only `panic` is on a nil pointer (`encoder.go:222-224`); `syncOwn l` holds
   `l ↦{dq}`, so `l ≠ nil`. `catchError` re-panics non-gob panics, but none is reachable for this
   type. A nil writer (`NewEncoder(nil)`, which Go allows) yields `ownEncoder enc nil`, unusable by
   `Encode` (it needs `ownEncoder enc (interface.ok e)` and `writeSink e`); a typed-nil writer needs
   the caller to prove its `Write`, which a panicking `Write` cannot meet.
6. **Writes after a failed `Write` (C1).** The spec's docstring says `Encode` stops at its first
   failed `Write`. False: `sendActualType` returns after a failed message but its caller's loop over
   struct fields/map key and elem continues and writes the next type's definition
   (`encoder.go:104-126`). Measured on `MSync` (8 messages): failing `Write` 2 gives 4 `Write` calls,
   failing 3 gives 5, failing 5 gives 6. The later pieces are messages of `bs` but not consecutive
   (the failed type's inner definitions are skipped). The spec still covers each such call:
   `writeSink` needs `S W2` (from the dead `∀ X, S X`) and `□ Q (W2 ++ piece)`, available with `W2`
   the prefix of `W ++ bs` before that piece. But if such a later `Write` **succeeds**, `writeSink`
   returns the live `S (W2 ++ piece)` and the dead state is gone, so a faithful derivation reaches
   `S (W ++ p1 p2 p3 p4)`, not the post's `S (W ++ bs)`. I tried to turn this into a panic: a writer
   that fails once then succeeds, with `S` live/dead through ghost state (`S Y := own γ (Excl Y) ∨
   tok`, the writer's invariant swapping them). It meets `writeSink`, and the client then holds the
   claimed `S (W ++ bs)` while the "real" ghost value is `W ++ p1..p4`; but nothing physical can be
   tied to `S`'s argument: an invariant tying it to the bytes written makes a success after the dead
   state unprovable for an arbitrary `W2` (the writer's `Write` must return `err = nil` and
   `S (W2 ++ piece)` for every `W2`), and without one the difference is ghost-only and no Go check
   can observe it. So no counterexample, but the post in the error case rests on writers whose
   failure is sticky (the kit's `*bufio.Writer`, `wire.wsink`), which `writeSink` does not say.
7. **Decode panics on arbitrary input.** The spec promises no panic for any bytes the reader
   returns (`I` is the caller's, the peers trusted only by the protocol proof). Gob's decoder
   recovers only `gobError` (`catchError`), so a runtime panic on malformed input would refute
   claim (6). The one explicit `panic` (`readMessage`, "non-empty decoder buffer",
   `decoder.go:98-100`) is unreachable: `recvMessage` is called only with an empty buffer.
   Fuzzed (`go test -fuzz`, go1.27.3, 5 minutes, 60,336,106 inputs, seeded with three valid
   `MSync` streams, decoding into a zero `MSync` through `bufio.NewReader(bytes.NewReader(data))`):
   no panic, no fatal error. The known gob decoder crashes (unbounded recursion on nested ignored
   types, CVE-2022-30635) are fixed in this toolchain (`maxIgnoreNestingDepth`). A malicious count
   cannot exhaust memory up front: `saferio.ReadData`/`SliceCap` grow allocations as bytes arrive.
8. **Aliasing in the decoded value.** `syncOwn l 1 m'` owns each command's `V` separately. Gob's
   `decodeMap` decodes every entry into one reused `elemP` but zeroes it after each entry
   (`decode.go:609-617`), so `decUint8Slice`/`decodeSlice` allocate fresh backing arrays per entry
   (no reuse of the previous entry's capacity): no aliasing. The target held zero maps (`l ↦ zero`),
   so `decodeMap` makes them.
9. **Tokens and concurrency.** `encoderTok`/`decoderTok` are `opaque` with no laws: not provably
   persistent or duplicable; `Encode`/`Decode` consume them and give nothing back, so no second
   `Encode` on one encoder (real gob would then omit the type definitions, breaking `wireBytes`'
   "fresh") and no concurrent use of one encoder or decoder is derivable. Two goroutines encoding one
   `MSync` (fractions `dq`) only read the maps (Go allows concurrent map reads); no one holds a
   writable share meanwhile. A `Write` that re-enters `Encode` on the same encoder has no token
   (and would deadlock on `enc.mutex` in Go, not panic). Concurrent `Decode`s over one
   `*bufio.Reader` are limited by the caller's `I`, not by these axioms.
10. **Cross-world entailment.** The pure laws mention no heap or location; the tokens are not pure
    equations. Not applicable.
11. **Inconsistency / the context (C3).** The pure axioms have a model (the real gob's set of
    streams, `fits` = value message under `tooBig`), by attacks 1-4. The triples are about the opaque
    function/method entries of names-only `encoding/gob`; like every names-only trust-boundary axiom
    they hold only in contexts where the names resolve to Go's code (as in
    `notes/axiom-review/dsv-inits/os-signal.md`, attack 8). Not specific to these axioms.

## Conditions

- **C1** (attack 6): the `Encoder__EncodeW` docstring ("stopping at the first failed `Write`") is
  false of go1.27.3. The post `S (W ++ bs)` when `err ≠ nil` is not justified for a writer whose
  `Write` may succeed after a failure; no panic follows from it (attack 6), and the kit's writer is
  sticky. Proposed restatement (not applied): make `writeSink`'s dead state sticky, e.g. a `Write`
  given the dead state returns an error and the dead state again, or weaken the error-case post to
  `∃ W', S W'`; at least correct the docstring.
- **C2** (attack 7): `Decode` promises no panic for any bytes, and gob's own documentation says it
  "does only basic sanity checking on decoded input sizes" (`decoder.go:24-27`). No input panicked in
  60M fuzzed executions, and the decoder catches only `gobError`s; the claim is supported by testing
  and code reading, not proved. In the deployment the stream's bytes are a verified peer's, so a
  narrower spec (no-panic only when the stream holds `wireBytes` streams) would suffice if this
  ever falls; not proposed now.
- **C3** (attack 11): the generic names-only context condition.

## Not tried

A Lean counterexample (no gap found to build one on); 32-bit platforms (`tooBig = 1 << 30`,
`int` 32-bit: `fits_of`'s margin would still hold, but Goose's `int` is 64-bit); `MSync` values over
about 2^31 bytes (memory).

No bug found in the Go code being verified (`MSync.Marshal` ignores `Encode`'s error on purpose, R7).
