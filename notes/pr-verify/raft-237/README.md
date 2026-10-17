# Files for the verification of etcd-io/raft#237

There are no Go tests or probes. The PR only removes a method, and the reviewer's checks were
`git grep` searches, listed below. Everything is run from this branch's worktree
(`pr-verify/raft-237`, which holds the translation of the fork branch `pr-raft-237-goose-lean`,
commit `d7b2b0826`, i.e. PR head `4a66f91bf8e4` applied to `raft37-goose-lean` `509271dac`).

| File | What it shows | Command |
|---|---|---|
| `rdeps.py` | the modules that import `Code.go_etcd_io.raft.v3`, directly or not: 1582, of which the `Link`/`Results` roots are printed. This is why only the raft and register roots were rebuilt. | `python3 -I notes/pr-verify/raft-237/rdeps.py . Code.go_etcd_io.raft.v3` |
| `build-summary.txt` | the build of the raft `Link`/`Results` and `examples.register.Results` roots against the new translation: 0 errors, 1907 jobs. The full 5.8 MB log is not kept. | `LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results Proof.github_com.mit_pdos.etcd_grove.examples.register.Results` |
| `results-axioms-pr.txt.gz` | the output of compiling `Proof/go_etcd_io/raft/v3/Results.lean` on this branch: 330 `#print axioms` results, none with `sorryAx` | `LAKE_ARTIFACT_CACHE=true lake env lean Proof/go_etcd_io/raft/v3/Results.lean` (after the build above) |
| `compare-axioms.py` | the 330 results are identical to `lean`'s. The `lean` side is read from the main checkout's `Results.trace`, where Lake compiled the module. | `python3 -I notes/pr-verify/raft-237/compare-axioms.py /shared/etcd-grove notes/pr-verify/raft-237/results-axioms-pr.txt.gz` (prints `IDENTICAL`, exit 0) |

The caller searches (empty apart from the method itself and `CHANGELOG/CHANGELOG-3.6.md:41`):

```
git -C ~/etcd grep -n -i quiesce raft-upstream/main pr-raft-237 -- '*.go'
git -C ~/etcd grep -n -i quiesce upstream/main origin/goose-lean -- '*.go'
grep -rn TickQuiesced Spec Proof etc notes issues
```
