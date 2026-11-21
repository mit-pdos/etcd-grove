---
upstream: none
checked: 2026-11-20
links: []
blocks-proof: no
---

# The bbolt fork rejects a readable 256 MiB value

**Impact:** On amd64, putting a 256 MiB value under the three-byte key `foo` fails with `ErrValueTooLarge` in upamanyus/bbolt at `3f8520bd`. The fork imposed a 256 MiB limit on the sum of the key and value lengths. This entry fits in a single leaf. The restriction affects applications even when the bucket has only one key.

**Reproduction:** Copy the test into the fork root and run the command below. It calls the public update and view APIs and compares the entire returned value with the original. The update failed at the old pin on the amd64 build VM. [Go regression test](bbolt-put-refuses-readable-entry/large_entry_test.go)

```sh
go test . -run '^TestBucket_Put_LargeReadableEntry$' -count=1
```

**Expected:** Put accepts the value, and a later read transaction returns the same bytes.

**Cause:** The fork applies a quarter-page-window limit to each entry so that four entries can always share a leaf. The split rule keeps those four entries together even when another leaf is available.

**Fix** The fork bounds a single entry by the address window measured from the leaf element. During spill it splits leaves whose combined serialized elements would exceed that window. The split may produce a leaf with one key. The fork tests cover the exact single-entry boundary and the split for two, four and five large values. The two-value database regression commits two values of 1 GiB minus one byte and reads both back. [Fork branch](https://github.com/upamanyus/bbolt/tree/goose-lean-leaf-size)

## Proof

The verified `Bucket.Put`, `node.splitTwo` and spill paths use the serialized prefix chosen by the splitter, including each element header. The previous entry bound implies the new file predicate by `entryBytesFit_legacy`. The bbolt results and link targets pass on the new pin.
