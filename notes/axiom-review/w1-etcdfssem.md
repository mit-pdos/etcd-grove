# W1 as `etcdFsSem`'s crash premise (`etcdCQ`) — adversarial review (2026-11-24)

Reviewed: `WalFs.W1 walCodec` (`Proof/go_etcd_io/etcd/server/v3/storage/wal/W1.lean`), as the crash premise of the
etcd examples' file semantics, `etcdFsSem := Fs.fsSemWithS etcdSQ etcdCQ`, `etcdCQ st st' := W1 walCodec st st'`
(`examples/lib/etcdstart/FsExts.lean`), branch `etcd-safe-crashskel/2026-11-24` (D6 Q2). By the D4c helper with the
`axiom` skill; analysis only (no counterexample program built, no run on configuration C).

## Verdict: **suspect, by design** — W1 is not a property of Linux on C; it excludes real crashes, of two classes,
both already listed in `W1.lean`'s docstring. No Go program was found whose panic the restriction hides **for the
programs of `etcd_safe`**; one exists in principle for an arbitrary program on a crashing machine (below).

## What W1 claims

At a crash `st → st'` of a machine, for every directory of the crashed tree and every suffix of its `.wal` files,
every frame a fresh WAL reader (`acceptsFiles walCodec`, CRC 0) accepts has its core (length word and record bytes)
**as of one change**: as of the last sync, or as of a change `n` by which each byte was last written by a `pwrite`
(not a resize) in `(0, n]`. It is a filter on the semantics' byte-wise crash mixes. Satisfiable (`W1Sat`: keep every
byte as synced), so it never removes every crash of a state: no execution gets stuck because of it.

## Attacks

1. **A CRC-32C collision on a torn frame** (W1's stated purpose). Real only with probability ~2^-32 per torn frame;
   etcd itself relies on the CRC to reject torn tails (`decoder.go:133-150`; the WAL W3 decision). The WAL tester's
   CP1 runs saw none. Accepted as the CRC's assumption: not attacked further.
2. **Unannounced zero tail** (W1.lean, "What W1 excludes beyond collisions"). A frame whose core's tail is zeros, of
   which only the first part has been `pwrite`n (the rest in the encoder's buffer), over preallocated zeros: if
   writeback persists the first part and the machine loses power, the file holds the **intended** frame, which the
   reader accepts. W1 excludes this image (the tail bytes are stamp 0, the head bytes stamped since the sync: as of
   no one change). **Real on C** (writeback of an unsynced `pwrite` is the kernel's normal behaviour; argued, not
   measured). For etcd: the image is byte-identical, in that file, to the image of a crash just after the encoder's
   next flush (which W1 allows: the zero tail is then `pwrite`n), so the member's recovery from it behaves as from
   an allowed crash. The two crash points differ in what else happened between them (other files, messages sent);
   etcd acknowledges an entry only after `Save`'s fsync, so nothing between them depends on the frame's durability.
   No panic of etcd found from it.
3. **A torn `Type` field over stale nonzero bytes** (W1.lean, the `N.tmp` reuse case,
   `nonissues/etcd-wal-cut-reuses-stale-tmp.md`). A frame across a sector boundary whose varint type comes back as
   the stale byte while the data and CRC are intact: the reader accepts a record of another type, no collision
   needed. W1 excludes it. Real only if a `.wal` file has nonzero bytes under a fresh frame, which the fork's `alloc`
   (`O_TRUNC`, F-Z's synced zeroing) rules out for etcd's files; the stale `N.tmp` is fsynced before it is named
   `.wal`. Not reached by etcd.
4. **An arbitrary program on a crashing machine** (the skill's question: a program that panics but is provable).
   W1 covers every `.wal` file of the machine, whoever writes it. A program that preallocates `x.wal`, fsyncs,
   `pwrite`s the head of a valid frame whose tail is zeros (never the tail), waits for writeback, and after a crash
   and restart panics iff the WAL reader accepts the frame, panics on C (attack 2) but is provable panic-free over
   `etcdFsSem` (every allowed crash image makes the reader reject: zeros, or a mix that fails the CRC). Not built
   (the proof needs the WAL decoder's reasoning over a crashing machine's closed theorem); the shape is the standard
   "excluded real crash" one. It is not a counterexample to `etcd_safe`, whose programs are fixed (etcd's member
   writes its own WAL only through the encoder), but it shows the premise is a claim about the deployment's
   programs, not about Linux.

## What follows for the statement

`etcd_safe` over `etcdFsSem` with `etcdCQ` covers the executions whose member crashes leave no WAL frame of classes
1-3. Class 1 is the CRC's assumption (accepted for the single-machine WAL tester, `tQ`); classes 2-3 exclude real
crashes that, for etcd's own code, lead to images W1 allows at another crash point or that etcd's file handling
does not produce. Recommended restatement (already planned in `notes/wal-fsext-plan.md`, "W1's target"): **no
CRC-32C collision on the `Data` of a frame whose bytes under it were zero**, with the non-`Data` bytes and the zero
tail proved from wire facts; it would retire classes 2-3 and make the premise the CRC's alone.

Not tried: a measurement on C (`fs-config/`); a Lean counterexample (attack 4).
