# porcupine, vendored

`github.com/anishathalye/porcupine` **v1.3.1** (commit `97cd067defd99df172053ba7f4ca5bbae57fe446`),
the version etcd's robustness tests use (`tests/go.mod`), with its non-test sources
(`*.go` but `*_test.go`, `visualization/`, `LICENSE.md`, `README.md`, `go.mod`).

Translated by `etc/goose.py` (project `porcupine`, configured by
`Code/github_com/anishathalye/porcupine.toml`) and verified in
`Proof/github_com/anishathalye/porcupine/`.

## The one change

Goose does not translate a labeled `break` out of a `select` inside a `for`. In
`checkParallel` (`checker.go`), the loop that collects the partitions' results

```go
loop:
	for {
		select {
		case result := <-results:
			count++
			ok = ok && result
			if !ok && !computeInfo {
				cancel()
				break loop
			}
			if count >= len(history) {
				break loop
			}
		case <-timeoutChan:
			timedOut = true
			cancel()
			break loop // if we time out, we might get a false positive
		}
	}
```

is written with a flag instead, which runs the same steps:

```go
	done := false
	for !done {
		select {
		case result := <-results:
			count++
			ok = ok && result
			if !ok && !computeInfo {
				cancel()
				done = true
			} else if count >= len(history) {
				done = true
			}
		case <-timeoutChan:
			timedOut = true
			cancel()
			done = true // if we time out, we might get a false positive
		}
	}
```

Upstream's tests (`porcupine_test.go`, `visualization_test.go`) pass on the changed copy
(checked 2026-10-14). No other file differs from upstream.
