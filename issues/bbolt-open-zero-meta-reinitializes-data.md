---
upstream: none
checked: 2026-11-20
links: []
blocks-proof: no
---

# bbolt fork reinitializes a nonempty database when both meta pages are zero

A writable Open on the verification fork can replace the first four pages of a damaged
database with an empty database and return success. Upstream validates the existing file.
The regression first appeared in the fork's interrupted-init recovery at 3207bac.

**Expected:** Open should preserve a file containing data inconsistent with interrupted
initialization and return the usual validation error. It should still complete an interrupted
first write on the next writable open.

**Impact:** Opening a file with two zeroed meta pages can destroy remaining data needed for
recovery. This affects users of the fork, including its bank example.

**Reproduction:** Copy the regression test into the root of upamanyus/bbolt at 3f8520bd.
Both cases fail on Linux. One file contains an unexpected byte in the fourth page. The other
extends past the fourth page. Both have zero meta pages. The test uses the public Open API and
checks the error and the file contents. [Go test](bbolt-open-zero-meta-reinitializes-data/init_image_test.go)

```
$ go test . -run '^TestOpen_PreservesUnrecognizedInitImage$'
--- FAIL: TestOpen_PreservesUnrecognizedInitImage/nonempty-leaf
    init_image_test.go:33: Open initialized a file containing bytes outside its init image
--- FAIL: TestOpen_PreservesUnrecognizedInitImage/past-last-init-page
    init_image_test.go:33: Open initialized a file containing bytes outside its init image
```

**Cause:** The fork classified the file by its first two pages. It then ran the new-database
initializer, which overwrote the freelist and root pages as well.

## Proof

The Open triple covers empty files and well-formed database images. A well-formed nonempty
image has a nonzero meta byte. The failure occurs outside that precondition.

## Fix

Commit 42c80a7 on the verification fork bounds recovery by the first write's length and
checks every byte present against zero or the corresponding first-write byte. The initializer
and recognizer use the same code to construct the freelist and root headers. The bank example's
older fork line carries the same change at 2e16636. A second test recovers a partial first
write using an 8192-byte page size.
