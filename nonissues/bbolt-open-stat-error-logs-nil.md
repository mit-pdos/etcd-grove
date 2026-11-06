---
upstream: none
checked: 2026-11-04
links: []
blocks-proof: no
---

# bbolt: `Open` logs `<nil>` instead of the `Stat` error

In `Open` (`db.go`, v1.5.0 line 270, and upstream `main` at `a4ef197`), when `db.file.Stat()`
fails the error is logged with the wrong variable:

```go
if info, statErr := db.file.Stat(); statErr != nil {
	_ = db.close()
	lg.Errorf("failed to get db file's stats (%s): %v", path, err)
	return nil, statErr
}
```

`err` is `Open`'s named result, nil at that point (the `openFile` and `flock` calls before it
succeeded), so the log line reads `failed to get db file's stats (...): <nil>`; the returned error
is the right one (`statErr`). The deferred `Opening bbolt db (...) failed: %v` line logs `err`
too, but `return nil, statErr` has set it by then, so that one is correct.

**Why not an issue:** a diagnostic only: the caller gets the right error, and the database is not
opened; no test (a failing `fstat` on an open descriptor cannot be produced on demand). Found by
code reading.

## Proof

no: `boltLogger` accepts a nil argument under `%v` (`logArgOk`'s `nil` case), so `Open`'s proof
covers the call as written; no premise.

## Notes

The fix is `statErr` in place of `err` in the `Errorf` call. Found 2026-11-04 by the bbolt proof
(U11b, `Open`'s owned phase).
