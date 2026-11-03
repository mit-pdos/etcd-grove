# Plan: organizing `examples/` (2026-11-03 · approved: option B with the proposed names)

**Decisions (the user, 2026-11-03):** option B (subdirectories by layer, renamed in the same move);
the proposed names; the headline theorems renamed with the directories; `durablekv` kept (moved to
`raft/kvfile`; whether `kvdurable` subsumes it is open). **Not yet landed:** the move waits for a
moment when few branches touch the examples ("there isn't a moment just yet when the development
is quiet"); `etc/move-examples.py` is prepared and dry-run meanwhile.

## What is there (surveyed at `lean` `c2794d5b2b`)

26 directories, flat, named by history (`putget3` = putget with 3 members; `linkv3p` = the
retired `linkv3` under partitions; `kvdurable` vs `durablekv`). By what they exercise:

| layer | examples (headline result) |
|---|---|
| **raft** (an application on `go.etcd.io/raft/v3`) | `kv` (`kv_porcupine_safe`), `kvreconf` (`kvreconf_porcupine_safe`), `kvdurable` (`kvdurable_porcupine_safe`), `durablekv` (translated, no proof yet; `notes/raft-durability-plan.md`), `kvwitness` (own module, part `RaftWitness/`) |
| **etcd** (server + client, through `examples/common`) | `putget`, `putget3`, `putgetc`, `restart3` (no result yet), `compactkv`, `watchkv`, `cachekv`, `leasekv`, `authkv`, `linkvtxn`, `linkv3p` |
| **kubernetes over etcd** | `k8setcd3` (own module), `k8sdaemonset` (own module) |
| **shared drivers / support** | `common` (start of etcd for the etcd examples), `lintest` (porcupine driver, own module, with its own instances `counter`, `logkv*`), `durable` (Go side of `durableExt`, used by the raft examples) |
| **OS / file extension** | `bboltfs`, `crashlog` |
| **not examples** | `axiomcx` (axiom counterexamples), `etcdbugs` (bug reproductions; not translated) |

What names a path: the Go import path `github.com/mit-pdos/etcd-grove/examples/<x>` becomes the
Lean module path (`{Code,GeneratedProof,Spec,Proof}/github_com/mit_pdos/etcd_grove/examples/<x>`:
1,520 `.lean` files, 1,586 files mention the module names, `pkg_id....examples.<x>` in specs),
`etc/goose.py`'s projects (`local`, `owned`), 46 files in `etc/` (link configs
`link-lean-first-*.txt`, tcb collections, `gen-init.py`, `gen-link.py`, `verified-code.py`,
`bounds-baseline.txt`), CI, ~550 mentions in `notes/`, the spec skill's examples, and every open
branch touching an example (425 branches, 10 worktrees).

## The decision: how much to move

**Option A — index and names in place (no move).** `examples/README.md`: the table above, each
example's one-line purpose, what it covers (raft / etcd server+client / which etcd features), its
headline theorem and its Go test; the same grouping in `notes/STATUS.md`'s example list. Cost:
one file. Leaves the flat directory and the historical names.

**Option B — subdirectories, one mechanical move (recommended).** `examples/raft/`,
`examples/etcd/`, `examples/k8s/`, `examples/lib/` (drivers), `examples/osfs/`, plus
`examples/README.md`. Renames done in the same move, so the churn happens once (below).
Cost: every module name under `examples` changes; done by a script, in one commit, at a quiet
moment (see "Doing it").

**Option C — B without renames.** Same churn as B, half the benefit. Not recommended: if we pay
for the move, rename at the same time.

## Proposed layout (option B)

```
examples/
  README.md            the index: per example, purpose, what it covers, headline theorem, test
  go.mod               unchanged (one module; k8s and lintest keep their own)
  raft/
    kv/                kv            (Put/Get/Append on raft; the minimal one)
    kvreconf/          kvreconf      (snapshots, conf changes, lossy network, read index)
    kvdurable/         kvdurable     (kvreconf made durable: crash and restart)
    kvfile/            durablekv     (kv made durable in one file; not verified -- or retire, below)
    kvwitness/         kvwitness     (own module; part RaftWitness/)
  etcd/
    putget/            putget        (one member: Put then Get)
    putget3/           putget3       -> or `cluster3`: three members
    compacted/         putgetc       (auto-compactor on)
    restart/           restart3      (a member stopped and restarted)
    compactwatch/      compactkv     (watch across compaction)
    watch/             watchkv
    cache/             cachekv
    lease/             leasekv
    auth/              authkv
    txnlin/            linkvtxn      (porcupine over the KV API with txns)
    partition/         linkv3p       (three members under network partitions)
    bugs/              etcdbugs      (reproductions; not translated)
  k8s/
    etcd3/             k8setcd3
    daemonset/         k8sdaemonset
  lib/
    etcdstart/         common        (starting etcd for the etcd examples)
    lintest/           lintest       (porcupine driver)
    durable/           durable       (Go side of durableExt)
  osfs/
    bboltfs/  crashlog/
  axiomcx/             unchanged name, moved under lib/ or kept at top (it is not an example)
```

The new names are proposals; the rule behind them: an etcd example is named by the feature it
exercises (`watch`, `lease`, `partition`), not by its ancestry (`linkv3p`); the directory says
the layer, so the name need not (`etcd/watch`, not `watchkv`). Theorem names follow the directory
(`etcd.watch_safe`?) -- **open question for the user**: rename the headline theorems too (they
appear in STATUS, notes and the tcb collections), or keep them.

## No new duplication

The move must not copy code, and it is the moment to record (not yet remove) what is already
duplicated:

- The raft KV family repeats `check.go`, `cluster.go`, `kv.go`, `cmd/`: `kv` vs `kvwitness` differ
  in 11/19/239 lines of check/cluster/kv; `kvreconf` vs `kvdurable` in 42/133/377; `kv` vs
  `durablekv` in 80/299/588. Each is a separately verified Go package (its Goose translation and
  proof are per package), so sharing code would mean a shared Go package with its own spec --
  a proof change, not part of the move. The plan only records the overlap in the README and in a
  follow-up (`raft/kvcommon`: the porcupine check and the cluster harness, whose proofs are
  already near-identical).
- The etcd examples already share `common` (to become `lib/etcdstart`); the Lean side shares
  `Proof/.../examples/common/`. Moving keeps exactly one copy of each: no per-layer copy of
  `common`, `lintest` or `durable`.
- `kvwitness` and `k8s*` have their own Go modules; their `replace` directives and
  `etc/goose.py`'s pin checks move with them, no second copy of the module files.
- The Lean side moves 1:1 (`Proof/.../examples/raft/kv/...`): no new shim modules re-exporting old
  names (they would be duplicated API to maintain).

`durablekv` (translated, no proof; part of `notes/raft-durability-plan.md`, overlapping
`kvdurable`): keep it, renamed; whether it still has a purpose next to `kvdurable` is the user's
call.

## Doing it (option B)

1. **Script, not hand edits** (`etc/move-examples.py`, kept for branches that land later): a table
   old path -> new path; it moves the Go directories (`git mv`), rewrites Go import paths, the
   `etc/` configs, `etc/goose.py`'s projects, CI, the spec skill's and notes' paths
   (`examples/<x>` and the module names), and the Lean source (`Spec/`, `Proof/`, `TrustedCode/`,
   `ManualProof/`, `RaftWitness/Proof/` hand-written files: module names, `pkg_id` paths). The
   generated `Code/`, `GeneratedProof/`, `Proof/<pkg>/Init.lean` and `Link.lean` files are not
   edited: `etc/goose.py`, `etc/gen-init.py`, `etc/gen-link.py` regenerate them.
2. **Check**: the gates (`etc/gates.sh`), plus: every headline theorem still exists with the same
   statement (modulo namespace) and `#print axioms` (the 47 collections, re-baselined only for
   paths); `etc/verified-code.py` counts the same functions verified; Go tests pass
   (`go test ./...` in each module).
3. **Timing**: every branch touching an example conflicts on rename. Land it when few branches are
   in flight (ask the other sessions), and keep the script so a branch made before the move is
   brought across by running it on the branch (`git merge` with rename detection handles moved
   files; the script handles the module names inside them).
4. **Notes**: old-to-new table in `notes/decisions.md`; STATUS's "Last updated"; historical notes
   keep their old names (append-only history), with the table to translate.

Estimated size: one large mechanical commit (~1,600 Lean files touched, ~100 Go files, ~50 config
files), a full rebuild of everything under `examples` (the bulk of the 12,000 jobs), one gates
run. Most of the effort is the script and its checks, a day or so.

## Naming rules (fixed for the script, after the survey)

- **Go package name = the directory's name** (`examples/etcd/cache` is `package cache`; Go allows
  importing etcd's `cache` from it). The Goose translation's Lean names follow the import path
  (`github_com.mit_pdos.etcd_grove.examples.etcd.cache`), so they cannot collide.
- **Hand-written Lean namespace = `<layer>_<dir>`** for the examples (`etcd_cache`, `raft_kv`,
  `k8s_etcd3`, `osfs_crashlog`): the bare directory names `cache`, `lease` and `auth` are already
  the namespaces of etcd's own packages' proofs (231, 9 and 34 files), and a short name an example
  shares with a package would make `open` ambiguous. The shared code keeps its namespaces
  (`common`, `lintest`, `durable`) though its directories move to `lib/` (`common`'s to
  `lib/etcdstart`): renaming `common` would touch every etcd example's references for no reader's
  gain.
- **Headline theorems = the namespace as prefix, the old suffix kept**: `cache_safe` ->
  `etcd_cache_safe`, `watch_adequate` -> `etcd_watch_adequate`, `kv_porcupine_safe` ->
  `raft_kv_porcupine_safe`, `putgetc_safe` -> `etcd_compacted_safe`, `crash_safe` ->
  `osfs_crashlog_safe`; the shared code's (`etcd_adequate`, `init_adequate`) unchanged.

## Dry run (2026-11-03, branch `examples-move`, worktree `/shared/etcd-grove-exmove`)

`etc/move-examples.py` on `lean` at `d572444cb6` (plus the branch's two preparatory changes below):
1,673 files moved, 1,901 rewritten, `examples/README.md` written (from `etc/move-examples-README.md`).
Then `etc/goose.py`, `etc/gen-init.py`, every `etc/gen-link.py` mode, `lake build` (12,020 jobs) and
`etc/gates.sh`: all passed, the trust base as on `lean` (781 axioms, 7 `sorry`s), 47 collections
matching; `etc/verified-code.py`'s summary identical before and after for all 29 projects; `go vet`
clean in all five Go modules. Five passes; each failure was fixed in the script, never in the
moved tree. What they taught the script:

- a namespace rename skips string literals (`go!"putget.etcd"` is a directory);
- `kv` is also an ordinary identifier (variables, fields, a nested `namespace kv` in `txnlin`): it is
  renamed only in its own files and their importers; the other old namespaces are unique and are
  renamed in every hand-written Lean file (the client's `kubernetes` proofs `open linkvtxn`);
- namespaces are also opened as `namespace EtcdGrove.kvdurable`, in multi-line `open`s, in `export`,
  and qualified as `EtcdGrove.<ns>.`; theorems as `Perennial.EtcdGrove.<name>` (`#print axioms`);
- `gen-link.py` hard-codes namespaces (its mode table, `LOCAL_INSTANCES`) and the link configs
  name functions `<last spec directory>_<fn>` and results `<ns>.wp_F`: both rewritten;
- the trust-base baselines name `sorry`s by namespace (`k8setcd3.revRoom` -> `k8s_etcd3.revRoom`).

Preparatory changes on the branch, landed with the move: `etc/verified-code.py` resolves a name
qualified by its package's spec namespace (it assumed the namespace was the package's last path
segment; after the move it is `<layer>_<dir>`); the index template. Found on the way and fixed on
`lean` (`d572444cb6`): `leasekv`'s cluster test called the renamed `common.NewServer`.

**Landing**, at a quiet moment: merge `lean` into `examples-move`, run the script, regenerate, gate,
compare `verified-code`, commit the move as one commit, fast-forward `lean`. A branch made before
the move: merge `lean` up to the commit before the move, run the script on it, then merge the move.
`/tmp` (a tmpfs) fills up under other sessions' tests: run with `GOTMPDIR` on `/shared`, and
re-run the gates if a check fails on temp files.
