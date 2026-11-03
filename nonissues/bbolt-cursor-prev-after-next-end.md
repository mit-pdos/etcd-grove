---
upstream: none
checked: 2026-11-03
links:
  - etcd-io/bbolt#733 issue closed: Prev at the first element; the fix made the cursor stay at the first element, the counterpart of this at the end
blocks-proof: no
---

# bbolt: `Cursor.Prev` after the end depends on how the end was reached

After `Seek` past the last key (nil returned), `Prev` returns the last key; after `Last` then
`Next` (nil returned), `Prev` returns the key *before* the last. `Next` at the last element
returns nil but leaves the cursor on the last element (an internal comment of `next` says so; the
public doc of `Next` only says nil is returned "at the end"), while `Seek` leaves it one past the
last. A user iterating forward then backward (`for k := c.First(); k != nil; k = c.Next() {}` then
`c.Prev()`) skips the last key.

**Why not an issue:** documentation and API behavior, not a reachable failure in etcd: etcd's
backend never calls `Prev` (its ranges are `Seek` then `Next`). The doc of `Next`/`Prev` could
state where the cursor stays, or `next` could step past the last element as `Seek` does.

## Proof

no: bbolt's API spec (2026-11-03, `Cursor.Next.spec`, `Cursor.Prev.spec`) models it
exactly: `Next` from position `i` moves to `i + 1` only below the end and otherwise stays at `i`;
`Prev` from `i + 1` moves to `i`.

## Notes

Test: `TestNextPastEndThenPrev` in
[`nonissues/bbolt-cursor-prev-after-next-end/next_past_end_prev_test.go`](bbolt-cursor-prev-after-next-end/next_past_end_prev_test.go)
(package `bbolt_test`), copied into the root of etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8
(2026-10-16), go1.27.3 linux/amd64 (the same on v1.5.0):

```
$ go test . -run TestNextPastEndThenPrev -count=1 -v
=== RUN   TestNextPastEndThenPrev
    next_past_end_prev_test.go:32: Seek past end, Prev: "c"; Last, Next: "", Prev: "b"
    next_past_end_prev_test.go:34: Prev after the end differs: "c" after Seek past the end, "b" after Next past the end
--- FAIL: TestNextPastEndThenPrev (0.00s)
```

The code there: `cursor.go`, `next`'s comment "it stays there and returns nil". Upstream not searched beyond bbolt#733. Found
2026-11-03 while specifying the cursor API.
