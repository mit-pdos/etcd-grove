# Files for the verification of etcd-io/etcd#21612

The report is `notes/pr-verify/etcd-21612.md`. The PR adds one unused struct field, so no Go test
or probe was written: there is no behavior to exercise. These files back the report's claim that the
existing proofs hold unchanged of the PR's code.

| File | What it shows | Revision | Command |
|---|---|---|---|
| `axioms-compare.log` | The `#print axioms` output of every result in mvcc's and txn's `Results.lean` (194 results) is identical on `lean` and on this branch: the same results, resting on the same axioms and `sorry`s. Also the downstream server/apply/v3rpc/read builds passing. | `lean` 51547df02 vs `pr-verify/etcd-21612` (translation of `mit-pdos/etcd-grove` branch `pr-etcd-21612-goose-lean`, b54ae1748) | `lake build --log-level=info Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Results Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Results > pr.log` on this branch; `lake env lean <Results.lean>` for each file on `lean`; then `python3 -I print-axioms-extract.py <log> \| sort -u` on each and `cmp` |
| `print-axioms-extract.py` | Extracts `(result, sorted axioms)` pairs from a Lean/Lake log | any | as above |
| `no-reader-check.sh` | The reviewer's check: with the field renamed, `go vet -composites ./...` type-checks all 14 workspace modules (with the `cluster_proxy`, `e2e`, `integration` and `cgo` tags too) without a type error, so nothing names `RangeOptions.Key` or builds an unkeyed `mvcc.RangeOptions{...}` (the only vet message is an unrelated `lostcancel` at `tests/framework/integration/cluster_proxy.go:54`). | `mit-pdos/etcd-grove` branch `pr-etcd-21612-goose-lean` (b54ae1748) | `TMPDIR=<scratch>/tmp no-reader-check.sh <fork checkout> <scratch>` |
