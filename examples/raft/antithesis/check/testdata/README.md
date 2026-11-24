# Differential-test fixtures

TLC's verdicts (through `antithesis-fm/tracekit/check/streamcheck.py`) on report streams, for
`diff_test.go`, which compares `check.Check`'s verdict with each and needs no Java:

- `verdicts.txt`, by `gen-fixtures.sh`: `traces/` (Antithesis's recorded streams, `antithesis-fm/traces/`),
  `mutations/` (their `scripts/mutate.py`'s 60 mutations, cut after the event TLC stops at), `sim/`
  (their simulator, `antithesis-fm/sim`, twelve modes, twelve seeds each);
- `verdicts-fuzz.txt`, by `gen-fuzz.py`: `fuzz/`, random perturbations of the recorded streams.

Line format: `source file config changed-index streamcheck-line`. The streams and the tools that made
them are antithesishq/etcd-raft-formalized's (commit `b3c7c16`, Apache License 2.0,
`third_party/etcd-raft-formalized/LICENSE`).
