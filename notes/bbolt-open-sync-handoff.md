# bbolt Open-sync pin bump: handoff (2026-11-11)

Branch `bbolt-open-sync` (worktree /shared/etcd-grove-rs3), cut from lean a259c0efd1.

Done: pin `ea4cab5` (upamanyus/bbolt `goose-lean-v2`), translation and examples' go.mod/go.sum;
`Open.wp_proof` over `fdatasync.spec` (Open/SyncAcc, Open/LogFmt, Link regenerated); the issue
`issues/bbolt-open-unsynced-meta-kill-then-power-loss.md`; `notes/decisions.md` "bbolt `Open` syncs
before its first commit"; STATUS entry.

Next: full build (flock, 64G cap), tcb --check, collections, interfaces (bbolt), gen-init --check,
goose --check, then etc/land.sh (LAKE_PACKAGES=/shared/tmp/manifest-ddc.json
PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc), merging lean first.
