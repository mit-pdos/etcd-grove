# etcd-raft-formalized, vendored (TLA+ only)

From [antithesishq/etcd-raft-formalized](https://github.com/antithesishq/etcd-raft-formalized), commit
`b3c7c16e9c21d973a53a2894c4c9f33131121cd2` (2026-11-20), directory `antithesis-fm/`, unmodified,
under the Apache License 2.0 (`LICENSE`, the repository's). Their README says the directory is
"almost entirely AI-generated", a research demonstration, not a maintained work.

| Here | There | What |
|---|---|---|
| `spec/EtcdRaft.tla` | `antithesis-fm/spec/EtcdRaft.tla` | the model (682 lines); the file their TLAPS proofs are about (`spec/proof/SPEC.sha256`: `eb73afdc…`) |
| `spec/EtcdBinding.tla` | `antithesis-fm/spec/EtcdBinding.tla` | the trace binding: report → model actions (795 lines) |
| `spec/EtcdBinding*.cfg`, `spec/manifest*.json` | same | the binding's configurations (3 or 5 servers, all or 3 voters, bootstrapped or empty logs) |
| `tracekit/tla/TraceKit.tla` | `antithesis-fm/tracekit/tla/TraceKit.tla` | the stream conventions the binding extends |

sha256: `EtcdRaft.tla` `eb73afdca4cb94e265110145e2e429af023f5507c6b9565ff5fc030215754e47`,
`EtcdBinding.tla` `eb81600143a4a24ead539a0626f6e5f87160ec716034db11dc2a17a44bec92d5`,
`TraceKit.tla` `1fc391b6d5d06468dc25fdc917aee6300ab4440176d342ed721dd9c237a4db09`.

Used by `examples/raft/antithesis/check`, a Go transcription of `EtcdRaft.tla` and `EtcdBinding.tla`
whose functions cite these files' line numbers (`notes/antithesis-check-design.md`). Not vendored:
their Lean/Veil model, TLAPS proofs, Go harness (`rawnode/`, `sim/`), and checker scripts; the
differential test's fixture generator (`examples/raft/antithesis/check/testdata/gen-fixtures.sh`)
runs those from a checkout.
