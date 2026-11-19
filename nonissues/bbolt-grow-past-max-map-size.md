---
upstream: none
checked: 2026-11-18
links: []
blocks-proof: no
---

# bbolt: a database that grows to the largest mapping can leave a file it cannot reopen

When the high-water mark of a database nears a mapping of `maxMapSize` (`0xFFFFFFFFFFFF` bytes on
amd64, 256 TiB), a commit's `DB.grow` truncates the file to `growSize + AllocSize` (`growSize` in
`db.go`: the requested size plus `AllocSize`, 16 MiB, once the mapping is above `AllocSize`), past
`maxMapSize`. The commit succeeds; but every later remap (`mmap(minsz)` maps
`mmapSize(max(fileSize, minsz))`) and every later `Open` of the file (`mmap(InitialMmapSize)`) fail
with "mmap too large", since `mmapSize` refuses a size above `maxMapSize`. So a database bbolt wrote
and closed can be impossible to reopen with bbolt.

**Why not an issue:** an absurd configuration: it needs about 256 TiB of pages in use (the mapping
reaches `maxMapSize` only above `maxMapSize - 1 GiB`), far past etcd's backend quota (8 GiB
recommended, `--quota-backend-bytes`). No test: found by code reading (session S3f of
`notes/bbolt-integration-plan.md`, while bounding the file's size for `Open`'s error-free spec).

## Proof

no: it shapes bbolt's specs, not the top-level results. `fileHolds` (what `DB.Close_own.spec` gives
back) bounds a file's size only by `2 ^ 62`; `Open_sharedNoErr.spec` takes the stronger
`fileHoldsM` (at most `maxMapSize` bytes), which a fresh file and a snapshot image meet
(`notes/bbolt-spec-decisions.md`, D-F2).

## Notes

A fix in bbolt would cap `growSize`'s result at `maxMapSize`.
