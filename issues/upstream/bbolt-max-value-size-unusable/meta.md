# bbolt-max-value-size-unusable: upstream candidate

- **Target**: etcd-io/bbolt.
- **Base**: upstream `main` a4ef19710eb7ddc41fd1155336baf331b5c57ba8 ("Update changelog for bucket related
  protection", 2026-10-16). `Put`'s checks (`bucket.go:540-546`), `WriteInodeToPage` (`internal/common/inode.go:80-81`)
  and `leafPageElement.Key`/`Value` (`internal/common/page.go:310-321`) unchanged since v1.5.0.
- **Branch**: `fix/bbolt-max-value-size-unusable` in `~/etcd-fixes/bbolt-max-value-size-unusable`
  (clone `~/etcd-bbolt`, remotes `upstream` etcd-io/bbolt, `origin` upamanyus/bbolt):
  - `1283e4e` bucket: test Put of a MaxValueSize value with a short key (`bucket_test.go`)
  - `668f5c0` bucket: reject a value too large to be stored with its key (`bucket.go`, and the doc comments of
    `ErrValueTooLarge` in `errors/errors.go` and `errors.go`)
  - No changelog commit (bbolt's `CHANGELOG/` entries are commits of their own, mostly by the maintainers).
- **Split**: the finding held two bugs. This candidate is the single entry (`Put` accepts a key and value that no
  page can hold); the several values on one page are `bbolt-large-values-leaf-unreadable` (its own finding and
  candidate). Independent branches off the same base: `git merge-tree --write-tree` of the two is clean
  (16bf905), and they touch different files (`bucket.go`/`errors*.go` vs. `node.go`), so the PRs carry no
  conflict note. They complement each other: with only the sibling's fix, a single entry too large for a page
  is still accepted (a node of one inode cannot be split); with only this fix, several values that each fit
  can still share one page.
- **Issue form**: bbolt has no issue template; `issue.md` keeps etcd's sections with a bbolt version section.
- **State**: draft. The fork `upamanyus/bbolt` does not exist yet (GitHub 404 on 2026-10-21): create it (fork
  etcd-io/bbolt) before `git -C ~/etcd-fixes/bbolt-max-value-size-unusable push origin
  fix/bbolt-max-value-size-unusable`; then check the issue's test link (`bucket_test.go#L1231-L1251`).

## Commands and results (go1.26.9 linux/amd64, 2026-10-23)

- At `1283e4e` (tests only), in a copy (`git archive`), one subtest at a time (a panic ends the binary):
  - `go test -count=1 -v -run 'TestBucket_Put_MaxValueSizeWithKey/^ab$' .`: `Commit` panics, `slice bounds out
    of range [::2147483648] with length 2147483647` in `WriteInodeToPage` (maxrss 2.1 GB, 4.6 s).
  - `-run 'TestBucket_Put_MaxValueSizeWithKey/^a$'`: `Expected error with "value too large" in chain but got
    nil`; the commit succeeded, and the btesting consistency check at close then fails, `slice bounds out of
    range [::2147483663] with length 2147483647`, and exits.
- Scratch test at the base (in a copy, values of `MaxValueSize` minus the given amount, 1-byte key unless said):
  key `ab`: `Commit` panics; key `a`: commit OK, `Get` panics (`[::2147483663]`); `MaxValueSize-16` and
  `MaxValueSize-32`: commit OK, `Get` returns the value. So the exact limit for one entry alone on a page is
  `len(key)+len(value) <= MaxAllocSize-16`; the fix's limit is 16 bytes tighter (below).
- At `668f5c0` (fix): `go test -count=1 -v -run 'TestBucket_Put_MaxValueSizeWithKey|TestBucket_Put_ValueTooLarge|TestDB_HugeValue' .`:
  all pass (`/a` 1.87 s, `/ab` 1.53 s: zeroing the 2 GiB value). `go test -count=1 . ./internal/... ./cmd/...`
  (TMPDIR on disk, `-timeout 40m`): all `ok` (root package 1608 s, run beside the sibling's suite). A first run
  failed in `TestOpen_Size_Large` with `disk quota exceeded` on a full tmpfs `/tmp` (an environment failure),
  a second timed out at the default 10 minutes with three suites running at once. `gofmt -l .`: nothing. `go vet .`: only
  `db_test.go:1507` (copies a lock), also at the base.
- Merged with the sibling (`git merge-tree`, clean): see the sibling's `meta.md`.

## check.py

`python3 -I .claude/skills/upstream-report/check.py bbolt-max-value-size-unusable`: no FAIL. WARNs kept: the doc comments of `ErrValueTooLarge` (documentation the fix must update); `Put` named in the issue (the API the issue is about).

## Duplicates (2026-10-21 and 2026-10-23, repo:etcd-io/bbolt, issues and PRs)

Searched `MaxValueSize`, `"slice bounds out of range" value`, `huge value`, `large value page split`, `is:pr
is:open value size`, `MaxAllocSize`: no report of this bug, no open PR. Related:

- #931 (closed): values above 256 MB panicked after a refactor shrank `MaxAllocSize` on 64-bit; fixed by #968
  (v1.4.1). This is the edge that remains at the restored bound. #950 (closed unmerged) was another attempt.
- #1044 (closed): `TestDB_HugeValue` panics on i386 in the same `WriteInodeToPage` slice (a 256 MB value, above
  the 32-bit `MaxAllocSize`). The maintainer (ahrtr) called it expected behaviour and fixed only the test
  (#1045). Relevant to the reception: the limit is `MaxAllocSize`, and this PR enforces it in `Put` as an error
  rather than leaving a panic; on 32-bit platforms it makes such a `Put` return `ErrValueTooLarge` too.
- #182 (closed, 2019): a slice-bounds panic in `leafPageElement.key` with 16-byte keys and values; corruption,
  not this.

## Why the fix works

A leaf page holding one entry is the page header (16 bytes), one element (16 bytes), the key and the value.
`WriteInodeToPage` slices `len(key)+len(value)` bytes from the data start through a `[MaxAllocSize]byte` array:
it panics when that sum exceeds `MaxAllocSize` (the `ab` case). `leafPageElement.Value` slices from the
element's address up to `pos+ksize+vsize`, `pos` being 16 for the only element: it panics when the sum exceeds
`MaxAllocSize-16` (the `a` case, after a successful commit). The fix rejects in `Put` any key and value with
`len(key)+len(value) > MaxAllocSize - PageHeaderSize - LeafPageElementSize`, i.e. whenever a page holding only
this entry would be larger than `MaxAllocSize`; every such page is then writable and readable.

## Why the test shows the bug and not a misuse

`Put` documents its errors (blank key, key too large, value too large); a value of `MaxValueSize` bytes is
within `MaxValueSize` by its doc ("the maximum length of a value"), and a 1- or 2-byte key within `MaxKeySize`.
The test is the existing `TestBucket_Put_ValueTooLarge` one byte smaller, with a short key; it asserts what
`TestBucket_Put_ValueTooLarge` asserts (`ErrValueTooLarge`), the outcome the issue expects.

## If a reviewer asks

Candidate layers and fixes:

1. **`Put` (chosen)**: one more check next to the existing ones, the same error, no API change; turns both
   panics (and, on 32-bit platforms, the #1044 one) into `ErrValueTooLarge`. This is the layer the maintainers
   chose for the same limit in #1044 (the limit is `MaxAllocSize`, a value above it is not supported).
2. **Lower `MaxValueSize`** (to `MaxAllocSize - 32 - MaxKeySize`, or per platform): an exported constant that
   changes value (per platform would make it differ between builds); the check is still needed for the key,
   unless `MaxValueSize` subtracts `MaxKeySize` and so rejects values that a short key can store today.
3. **Raise `MaxAllocSize` on 64-bit** (the array type `[MaxAllocSize]byte` could be larger): the constant #968
   just restored, used for the write chunk size in `tx.write` too; the element fields `pos`, `ksize`, `vsize` are
   `uint32`, so a limit remains; a larger change than this bug needs.
4. **Slice from the data start in `WriteInodeToPage` and `leafPageElement.Value`** (base pointer plus offset,
   slice `[0:size]`): removes the `-16` for reads and the sum for writes, but a single value still has to be at
   most `MaxAllocSize`, and a page still has its `uint32` positions; not needed once `Put` bounds the entry.

The limit is the whole page (`-32`) rather than the exact read bound (`-16`): it is the simpler statement ("a page
holding only this entry fits in `MaxAllocSize`"), and it is the bound the sibling's split relies on for a
single-inode page. It rejects 16 bytes' worth of key-plus-value lengths (`MaxAllocSize-31` to `MaxAllocSize-16`)
that commit and read back today; values of about 2 GiB, which a reviewer may prefer to keep, at the cost of
the exact `-16` (`LeafPageElementSize` only) in the check.

`ErrValueTooLarge`'s doc ("larger than MaxValueSize") is extended in both places it is declared. `MaxValueSize`'s
doc ("the maximum length of a value") is left: it stays the maximum; on 64-bit platforms a value of exactly
that length can no longer be put with any key. A reviewer may want that said in its doc.

Other callers: `Put` is the only path that stores a user value (`CreateBucket` stores a bucket header,
`MoveBucket` moves one); `Compact` copies through `Put`, so compacting a database with an entry over the limit
(possible only from the base's `a` case, which cannot be read anyway) now fails with the error instead of
panicking.

The test allocates a 2 GiB zero value (lazily: it is never written with the fix) and is skipped on DroneCI as
`TestBucket_Put_ValueTooLarge` is. On 32-bit platforms `make([]byte, MaxValueSize)` fails as in that test.
