# bbolt-spec-test

Tests bbolt's trust-boundary specs (`Spec/go_etcd_io/bbolt/`, over the predicates of
`Proof/go_etcd_io/etcd/server/v3/storage/backend/InvBbolt.lean`) against the real bbolt v1.5.0, by
spec-guided random call sequences (step 2 of `notes/spec-first-plan.md`; `main.go`'s comment says
how). Each step of `main.go` transcribes one axiom by hand; keep them in step with the Lean files.

    go run . -runs 10000             # the current statements: no refutation expected
    go run . -old-wbkt               # wBkt without a generation, as before 2026-10-27 (false)
    go run . -old-info               # DB.Info_kv as before audit B4b (false)
    go run . -old-cursor-kvw         # Bucket.Cursor_kvw as before audit B4b (false)
    go run . -mutant seek-gt         # deliberately wrong specs, see -help

`-seed N -runs 1` replays one run; `-v` prints every run's calls. Exit status 1 on a refutation.
