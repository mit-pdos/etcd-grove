# bbolt Open-sync pin bump: handoff (2026-11-11)

Branch `bbolt-open-sync` (worktree /shared/etcd-grove-rs3), cut from lean a259c0efd1.

Done (commit "bbolt pin -> c5a6065d (WIP)"): `etc/goose.py` bbolt rev c5a6065d2380 with its
comment; `Code/go_etcd_io/bbolt.lean` regenerated (Open.impl gains the `fdatasync` block, line
comments shift by 14); `examples/go.mod`/`go.sum` replace bbolt by the same commit (h1 sums from
`go mod download`; `go mod verify` and `go build ./...` clean). Not built.

Blocked: `Open.wp_proof` (Proof/go_etcd_io/bbolt/Open.lean). The new call sits after
`loadFreelist`, whose `DB.loadFreelist.spec_open` has already published the halves of `opened`,
`freelist`, `ops.writeAt` (metaR, in `metalock`) and of the mapping fields (Pm, in `mmaplock`).
The error branch's `db.close()` (no locks) writes those fields, so needs the halves inside the
locks: not provable without `Lock` (isMutex is sealed). The success branch is easy (fdatasync's
resources from `wdbCore`, `m` -> `m'` with the same size and maps).
Options (for the coordinator / user): the fork's error branch calls `db.Close()` (as the
`txErr` branch does), or the sync moves before `mmapUnlocked`/`loadFreelist`.

Next: once the fork commit is settled, rebump, prove, land the issue (draft in
/shared/tmp/bbolt-fix/issue/), STATUS entry, gates, land.sh.
