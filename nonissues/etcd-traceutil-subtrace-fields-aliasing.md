---
upstream: none
checked: 2026-11-23
links: []
blocks-proof: no
---

# traceutil: a long trace's log can show a subtrace step with another step's fields

`(*Trace).logInfo` merges a subtrace's common fields into each of its steps with
`t.steps[j].fields = append(tstep.fields, t.steps[j].fields...)`, once per step `j`, all from
the same `tstep.fields`. When that slice has spare capacity, every `append` writes the same spare
array in place, so the steps' new fields slices share it and each later step overwrites the fields
an earlier one shows: the logged line of an earlier step carries a later step's fields. A subtrace
marker's fields have spare capacity when the caller passed `StartSubTrace`/`StopSubTrace` a slice
with spare capacity, or when a start marker is inside an enclosing subtrace (two `StartSubTrace`
without a `StopSubTrace` between them): the enclosing marker's merge, which runs first, gave it a
slice `append` allocated, whose capacity Go rounds up.

**Why not an issue:** no test, found by code reading; etcd meets the precondition: its only
caller, `executeTxn` (`server/etcdserver/txn/txn.go`), passes three-field literals (no spare
capacity) and closes each subtrace before opening the next (a nested `Txn` opens its own in
turn, sequentially), so no marker's fields have spare capacity when they are merged. Only the
log's text would be wrong.

## Proof

no: `LogWithStepThreshold`'s spec says nothing of the logged text. The proof of `logInfo`
(`Proof/go_etcd_io/etcd/pkg/v3/traceutil/LogLemmas.lean`, regions) follows the aliasing: it owns
the arrays rather than the steps' slices, so that the merge may write in place.

## Notes

A fix: `append(tstep.fields[:len(tstep.fields):len(tstep.fields)], t.steps[j].fields...)` (or
`slices.Concat`), so each step gets an array of its own.
