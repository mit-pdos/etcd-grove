# bbolt-large-values-leaf-unreadable: upstream candidate

- **Target**: etcd-io/bbolt.
- **Base**: upstream `main` a4ef19710eb7ddc41fd1155336baf331b5c57ba8 ("Update changelog for bucket related
  protection", 2026-10-16). `splitTwo`/`splitIndex` (`node.go:229-291`) and `leafPageElement.Value`
  (`internal/common/page.go:317-321`) unchanged since v1.5.0.
- **Branch**: `fix/bbolt-large-values-leaf-unreadable` in `~/etcd-fixes/bbolt-large-values-leaf-unreadable`
  (clone `~/etcd-bbolt`, remotes `upstream` etcd-io/bbolt, `origin` upamanyus/bbolt):
  - `e8f9d2b` node: test splitting a node larger than MaxAllocSize (`node_test.go`)
  - `b71c0a2` node: split a node too large to be read back from one page (`node.go`)
  - No changelog commit (bbolt's `CHANGELOG/` entries are commits of their own, mostly by the maintainers).
- **Split**: from `bbolt-max-value-size-unusable` (one entry too large for any page, fixed in `Put`). Independent
  branches off the same base; `git merge-tree --write-tree fix/bbolt-max-value-size-unusable
  fix/bbolt-large-values-leaf-unreadable` is clean (16bf905), different files, so no conflict note in the PRs.
  They complement each other: this split cannot help a node of a single inode, so a single entry too large for
  a page needs the sibling's check in `Put`; with both, every page bbolt writes fits in `MaxAllocSize`.
- **Issue form**: bbolt has no issue template; `issue.md` is free-form prose, no headings (the 2026-10-23 review).
- **State**: draft. The fork `upamanyus/bbolt` does not exist yet (GitHub 404 on 2026-10-21): create it (fork
  etcd-io/bbolt) before `git -C ~/etcd-fixes/bbolt-large-values-leaf-unreadable push origin
  fix/bbolt-large-values-leaf-unreadable`; then check the issue's test link (`node_test.go#L171-L188`).

## The test is not the example

The issue's example is an end-to-end test (`TestDB_HugeValues`, given in full in the issue): two values of
`MaxAllocSize/2` bytes under `a` and `b`, committed, then read back. Its cost: at the base it fails (panics in
`Get`) with maxrss 5.3 GB in 11 s; with the fix it passes with maxrss 8.9 GB in 25 s, and under `-race` it reached
23 GB (and filled a tmpfs `/tmp`). The CI runs `ENABLE_RACE=true make test` on runners of 16 GB, and bbolt has no
race build tag to skip it, so a test of that size cannot go in the branch. The branch's test is the same data at
the layer of the defect: a node holding the two values (sharing one untouched 1 GiB slice, so no memory) must
split into pages of at most `MaxAllocSize` bytes, the bound the readers need. It is in the style of the
`TestNode_split*` tests next to it. The end-to-end test was run at the base and at the fix (above) in the
worktree before it was replaced (its code is in `issue.md`, next to `TestDB_HugeValue` in `db_test.go`).

## Commands and results (go1.26.9 linux/amd64, 2026-10-23)

- At the base, `TestDB_HugeValues` (end-to-end): `panic: runtime error: slice bounds out of range
  [::2147483664] with length 2147483647` in `leafPageElement.Value` ← `Cursor.keyValue` ← `Cursor.seek` ←
  `Bucket.Get`. With the fix: `--- PASS: TestDB_HugeValues (20.63s)`.
- At `e8f9d2b` (tests only): `go test -count=1 -v -run TestNode_split .`: `node_test.go:185: exp<=2147483647;
  got=2147483710`, `--- FAIL: TestNode_split_MaxAllocSize`; the other `TestNode_split*` pass.
- At `b71c0a2` (fix): `TestNode_split*` all pass. Scratch test (in a copy, not in the branch): every leaf of 1 to
  7 inodes, each of 100 bytes, `MaxAllocSize/3`, `MaxAllocSize/2` or `MaxAllocSize-40` (21844 combinations),
  split with a 4096-byte page: no empty node, order and inodes kept, every node of two or more inodes at most
  `MaxAllocSize` (0.24 s). `go test -count=1 -timeout 40m . ./internal/... ./cmd/...` (TMPDIR on disk): all `ok`
  (root package 1611 s; a first run with the default 10-minute timeout timed out, three suites running at once). `gofmt -l .`: nothing. `go vet .`: only `db_test.go:1507` (copies a lock), also at the base.
- Both fixes merged (`git merge-tree` result 16bf905, in a copy): the two branches' tests and `TestNode_split*`,
  `TestBucket_Put_ValueTooLarge`, `TestDB_HugeValue` pass. A scratch end-to-end test there: three values of
  `MaxAllocSize-40` bytes under `a`, `b`, `c` (about 6 GiB in one bucket, past the `uint32` positions' 4 GiB) in
  one `Update`, then `Get` of each (length, first and last byte) and `Tx.Check`: passes (86 s, maxrss 23 GB).
- `GOARCH=386 go vet .`: clean. `GOARCH=386` tests do not run at the base either: `TestNode_split` panics
  `unaligned 64-bit atomic operation` in `TxStats.IncSplit` (the cross-arch CI only builds): a regression on
  `main` from 4bfc851, recorded as `issues/bbolt-txstats-unaligned-32bit.md`; so neither branch's test was run on
  a 32-bit platform.

## check.py

`python3 -I .claude/skills/upstream-report/check.py bbolt-large-values-leaf-unreadable`: no FAIL. WARNs kept: the comments (one extends the existing guard comment, one rewords the loop comment it changes, one says why the new break exists); "split" in the issue (plain English, "split into pages"); the PR's 96 words (about 35 of them the fixed sentences).

## Duplicates (2026-10-21 and 2026-10-23, repo:etcd-io/bbolt, issues and PRs)

Searched `MaxValueSize`, `"slice bounds out of range" value`, `huge value`, `large value page split`, `is:pr
is:open value size`, `MaxAllocSize`: nothing on several values sharing a page, no open PR. Related, different:
#931/#968 (one value above a shrunk `MaxAllocSize`), #1044 (one value above the 32-bit `MaxAllocSize`, called
expected), #182 (a slice-bounds panic in `leafPageElement.key` with 16-byte values: corruption), #422 (open:
customizing the rebalance threshold).

## Why the fix works

At the base, `splitTwo` returns a node of at most four inodes unsplit whatever its size, and `splitIndex`
forces two inodes onto each page (it breaks only once `index >= MinKeysPerPage`). A leaf page's element `i` is
read by slicing from the element's address up to `pos+ksize+vsize` through a `[MaxAllocSize]byte` array, i.e. up
to the end of that element's value; on a page larger than `MaxAllocSize`, the later elements' values end beyond
`MaxAllocSize` bytes from their element (two inodes of 1 GiB: `b`'s ends at 2147483664) and every read panics.

The fix: (1) `splitTwo` does not skip the split of a node of two or more inodes that is larger than
`MaxAllocSize`; (2) `splitIndex` stops before an inode that would take the first page past `MaxAllocSize`, once
the page has one inode; (3) `splitIndex`'s loop runs to at least index 1, so that a node of two to four inodes can
be split after its first inode (the loop's bound, `len - MinKeysPerPage`, is 0 to 2 there). Each split's first
page is then at most `MaxAllocSize` (one inode, which the sibling's `Put` check bounds, or inodes within the
threshold), and `split` re-splits the rest the same way. Every node that fits in `MaxAllocSize` splits exactly
as before: (1) and (2) apply only to larger nodes, (3) only to nodes of at most four inodes, which reach
`splitIndex` only when larger than `MaxAllocSize`.

The `MaxAllocSize` check in `splitTwo` runs only when the base's guard would return early (at most four inodes,
or a node smaller than a page), so it costs no more than `sizeLessThan(pageSize)` already does; the check in
`splitIndex` is one comparison per inode it visits. The split of a large node stays linear.

## Why the test shows the bug and not a misuse

Two `Put`s of values within `MaxValueSize`, in one `Update`, then a `Get` in a `View`: ordinary API use. The
unit test asserts the property the readers need (no page over `MaxAllocSize`), with the example's sizes.

## If a reviewer asks

Candidate layers and fixes:

1. **The split (chosen)**: pages never exceed what the readers can address, so every value that commits can be
   read, for any number of large values; no on-disk format change (leaves of one key already exist, e.g. after
   deletes: `minKeys()` is 1 for a leaf). Behaviour unchanged for every node that fits in `MaxAllocSize`.
2. **Slice from the data start in the accessors** (`leafPageElement.Key`/`Value`, `branchPageElement.Key`: base
   pointer `elem+pos`, slice `[0:size]`): the smallest change, and it fixes the reproduced panic, but `pos` is a
   `uint32` offset from the element, and a leaf of three or four values near 2 GiB (allowed by the unsplit
   four-inode node) puts a value more than 4 GiB from its element: the position wraps and the read returns other
   bytes silently. It would need the split anyway (or a panic at write time).
3. **Lower `MaxValueSize`** (so that four maximal entries fit in `MaxAllocSize`: about 512 MiB on 64-bit): an
   exported constant; rejects single values between 512 MiB and 2 GiB that work today (#931's user had a value
   above 256 MB).
4. **Reject in `Put` a value that would share a page with a large neighbour**: `Put` does not know the page
   layout, which `spill` decides at commit.

Rebalance: a leaf of one large inode is below `minKeys` only if it has none, and a rebalance merge of two large
leaves (after a delete) is re-split by the spill that follows in the same `Commit`. Branch nodes hold keys only
(at most `MaxKeySize`), so their size never comes near `MaxAllocSize`.

The test shares one 1 GiB zero slice between the two inodes and never writes it, so it needs no memory; on
32-bit platforms `MaxAllocSize/2` is 128 MiB, also unwritten.
