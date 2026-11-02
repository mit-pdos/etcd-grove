# porcupine PR #46, vendored

anishathalye/porcupine pull request #46, "Support system-specific consistency models via
DAG-based execution": head `29a6b8e6cde077c5b53d9d15ba7b7c6d0fad0d16` of
`practical-systems-iitd/porcupine`, branch `master` (unmerged, 2026-11-02), with its non-test
sources (`*.go` but `*_test.go`, `visualization/`, `LICENSE.md`, `README.md`, `go.mod`). Beside
`third_party/porcupine` (v1.3.1), which it does not replace.

Translated by `etc/goose.py` (project `porcupine-dag`, configured by
`PorcupineDag/Code/github_com/anishathalye/porcupine.toml`) into the parallel tree
`PorcupineDag/` (the Go path is v1.3.1's) and verified in
`PorcupineDag/Proof/github_com/anishathalye/porcupine/` (`notes/porcupine-dag-plan.md`).

## The one change

The same as v1.3.1's (`third_party/porcupine/UPSTREAM.md`): Goose does not translate a labeled
`break` out of a `select` inside a `for`, so the loop of `checkParallel` (`checker.go`) that
collects the partitions' results breaks with a flag `done` instead, running the same steps.
No other file differs from the PR's head.
