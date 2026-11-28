# fs-link: SaveDBFrom's link assumptions measured on C (2026-11-28)

The assumptions (i)-(iii) of the axiom `snap.Snapshotter.SaveDBFrom.wp_proof`, stated and argued
in `examples/osfs/semantics/meta_link_no_replace.go` (i), `meta_link_crash.go` (ii) and
`meta_link_shared_inode.go` (iii). **No contradiction**: every state the runs produced is one the
examples allow.

**Host.** fk-lean2 (AWS, x86_64), kernel `7.0.0-1017-aws`, go1.27.3. `check.sh` on every
filesystem used: "is C (kernel 7.0.0-1017-aws, ext4, block size 4096, options rw, ..., dioread_nolock,
nodiscard, delalloc, journal_checksum, barrier, auto_da_alloc, ..., data=ordered, ...)", with
`commit=5` (the default) for the live tests and `commit=1` (which C allows) under dm-log-writes.
Filesystems made by `fs-config/mkfs-mount.sh` on loop devices (1 GiB images, `mkfs.ext4` defaults).

## (i) link never replaces: live, on C

`examples/osfs/semantics/run-models-on-c.sh -run TestLink -v`:

- `TestLinkNeverReplaces`: PASS (EEXIST; the existing name's inode, nlink 1 and bytes unchanged).
- `TestLinkRaceOneWins`: PASS, 5000 rounds of two concurrent links to one free name: first link
  won 12, second 4988; never both, never neither.
- `TestLinkSharedInode`: PASS (after the link one inode, nlink 2 for both names; after the removal
  nlink 1, bytes kept).

## (ii), (iii): crash states under dm-log-writes

`link.sh WORKDIR SCENARIO [commit=1] [SLEEP_MS]` (SaveDBFrom's exact calls: create `tmp1`, write
64 KiB, fsync, close, link to `0000000000000005.snap.db`, unlink `tmp1`, fsync the directory),
`lreplay.py` replaying the log to every flush/FUA entry, recovering by a kernel mount and checking
the root. Five runs per scenario: two with the default 1.2 s pause between calls, three with
round 5's 2.5 s.

| scenario | runs | crash points | distinct images (union) | violations |
|---|---|---|---|---|
| `snapsave` | 5 | 134 (26, 26, 28, 26, 28) | 5: empty; `tmp1` 0 bytes; `tmp1` stream; `tmp1`+`.snap.db` one inode nlink 2 stream; `.snap.db` nlink 1 stream | 0 |
| `snapsave-exist` | 5 | 104 (20, 20, 20, 22, 22) | 3: old; old + `tmp1` 0 bytes; old + `tmp1` stream | 0 |

Per crash point, by the last returned call before it (`snapsave`, 2.5 s runs; counts per run):

| after | images |
|---|---|
| start, create | empty; `tmp1` empty |
| write, fsync of `tmp1` | `tmp1` empty (before the fsync's commit); `tmp1` with the stream |
| link | `tmp1` alone (link not yet committed: 1 point); `tmp1` + `.snap.db`, one inode, nlink 2, stream (1 point) |
| unlink | both names, one inode (1 point); `.snap.db` alone, nlink 1, stream (1 point) |
| directory fsync | `.snap.db` alone, nlink 1, stream (15 points) |

- **(ii)** The `.snap.db` was absent, or held the whole 64 KiB stream, at every one of the 134
  points; never a prefix, size 0 or another file's bytes; after the directory fsync it was always
  there with the stream (in the 1.2 s runs too).
- **(iii)** Both names on one inode (nlink 2, the stream) appeared after the link's commit and
  before the unlink's in the four runs where the two calls committed separately (all three 2.5 s
  runs and one 1.2 s run); in the other 1.2 s run the link and the unlink committed in one
  transaction (the image went from `tmp1` alone to `.snap.db` alone), also allowed. Never two
  inodes, never `.snap.db` with nlink 1 while `tmp1` was there, never the removal kept without the
  link (no image without `tmp1` and without the `.snap.db` after the write), never `tmp1` after the
  directory fsync.
- **snapsave-exist** (the link fails with EEXIST): the existing `.snap.db` stayed "old", nlink 1,
  its inode, at all 104 points; `tmp1` was always a different inode, and gone after the directory
  fsync.

**Limits** (as round 5, B1): the replay takes the writes in completion order and cuts only at
flushes/FUA; reorderings between flushes are not explored. Recovery is the kernel's (a mount),
not `e2fsck`.

**Harness change.** `lreplay.py` now also prints, for each mark, the images of the crash points
after it and their counts (the first-seen list hid which states occur after which call). No other
change was needed; the harness ran as written.
