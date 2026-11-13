# auth-safe S2: handoff (the closed theorem `etcd_auth_safe`, 2026-11-13)

Stage S2 of the `etcd_auth_safe` Scope (`/shared/tmp/auth-safe/scope.md`, §4) for etcd-grove-81.
Worktree `/shared/etcd-grove-authfix`, branch `auth-safe-s2` (from lean 51ee20f154). Scratch:
`/shared/tmp/auth-safe-s2/`.

## Done

- `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/Adequacy.lean`: `authkvProgram`,
  `authkvNames`, `etcd_auth_adequate`, a copy of `watch/Adequacy.lean` at authkv's program
  (`auth.initialize' #() ;; Main #()`), address `127.0.0.1:23916`, data directory `authkv.etcd`, member
  `authkv`, with the extra hypothesis `hD22 : ∀ hG, ⊢ authSchemaSrv` (D22, a named hypothesis). It
  links `etcd_auth.wp_Main` over `startServer.wp_proof … (server_new_auth_on (hD22 hG)) server_Start`
  inline (Results imports Adequacy, so it cannot use `authkv_Main`).
- `Results.lean`: `etcd_auth_safe` (restatement, docstring "What the result does not say", the
  Scope's §3), `#print axioms` of both; header fixed (no sorry, no `ValidSpec`).
- D5 stale headers: `etc/tcb-collections/authkv.txt`, `auth/Main.lean` (Proof and Spec),
  `auth/Defs.lean` (`authkv.etcd`), `auth/Results.lean`; `examples/README.md` row.

## Next, in order

1. Full build (log `/shared/tmp/auth-safe-s2/full-build1.log`), `etc/tcb-report.py --collection
   etc/tcb-collections/authkv.txt --check` (expect only additions: the initializers' axioms, the
   closed theorem's environment axioms), then `--check --update` on authkv only; compare with putget
   (`--roots etcd_putget_safe` against `--roots etcd_auth_safe`).
2. `etc/gates.sh` (GOWORK unset), STATUS entry (oldest to status-history, append only).
3. Merge lean, STOP for 81's review before `etc/land.sh`.

## Build command

`export TMPDIR=/shared/tmp; flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p
MemoryMax=64G python3 etc/timed-build.py --packages=/shared/tmp/manifest-ddc.json`
