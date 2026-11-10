# Premise fixes 2: handoff

Branch `premise-fixes-2`, worktree `/shared/etcd-grove-pf2`, off lean `9ca174a34d`. Fix 5 of the
premise attack, option 1 (approved by the user via etcd-grove-81): the raft fork's fourth fix,
`ConfState.Equivalent` comparing configurations instead of `proto.Equal`.

## Build command

```
export TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json
flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```

## The fork commits (local, never pushed: the user pushes them)

- raft: `/shared/tmp/premise-fixes-2/raft`, branch `raft37-goose-lean-a2`, commit `d2c16c5`
  (on `565c2bd`).
- witness: `/shared/tmp/premise-fixes-2/raft-witness`, branch `raft-witness-goose-lean`, commit
  `3e3ed2d` (on `99cb9e2`; also compares `Witness`/`WitnessOutgoing`).
- `etc/goose.py` pins both; `examples/{go.mod,k8s/*/go.mod,raft/kvwitness/go.mod}` and their
  `go.sum` name the pseudo-versions (hashes computed from the local commits, served through a local
  bare repo with `GIT_CONFIG_*` insteadOf; the same once pushed). CI's `goose.py --check` and
  `go mod download` need the commits pushed.

## Done

Translations regenerated with `--src`; `confStatesEqual`/`idsEqual`/`boolOf` (and witness
`uint64Of`) specified and proved; `Equivalent` re-proved over them; `proto.EqualConfState` deleted
in both trees; the link lists and Links regenerated; `examples/premisefix/confstate` asserts the
new behavior; `nonissues/raft-confstate-unknown-fields-panic.md` updated.

## Checked (2026-11-10)

Full build green (13637 jobs); `etc/gates.sh` (with `RAFT_SRC`/`RAFT_WITNESS_SRC` naming the local
fork checkouts and `GOPROXY=off`) passed every gate but two that need the fork commits on GitHub,
both rerun green against local copies: `goose` (`etc/goose.py --check` after the witness module
was in the module cache: 40 projects up to date) and `reader-slot` (it reads `.lake/goose/raft{,-witness}`,
which `--src` does not fill: cloned there from the local checkouts). Trust base 845 axioms, 4
`sorry`s (`proto.EqualConfState` gone; 21 collections updated). Stopped before `etc/land.sh`: the
user pushes the fork branches first.

## Not done (scope change, see `notes/decisions.md`, "Premise fixes 2")

`csPts` keeps `[]`: stage A already made the decode path sound; relaxing it is for etcd-grove-81 to
schedule.

## Pitfalls

- Never edit files a running build imports.
- A hand-written comparison must list every field (the witness fork has two more).
