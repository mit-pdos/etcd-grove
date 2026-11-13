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

## Checked (2026-11-13)

Full build ok (17476 jobs, `/shared/tmp/auth-safe-s2/full-build1.log`); `etc/tcb-report.py --check`
matches the baseline (870 axioms, 4 sorries); `authkv.txt` `--check --update`: +237 axioms, none
removed (the closed theorem's initializer/program-start axioms); `etc/gates.sh` all passed
(`/shared/tmp/auth-safe-s2/gates1.log`). Trust base against putget (`--roots`, files
`/shared/tmp/auth-safe-s2/roots-{auth,putget,watch}.txt`): etcd_auth_safe 658 axioms, putget 620;
only putget: `auth.NewAuthStore.wp_proof`; only authkv: 39 (all already in authkv's collection
before S2). No sorry.

## Next

Merge lean, STOP for 81's review of the new closed statement, then (GOWORK unset)
`LAKE_PACKAGES=/shared/tmp/manifest-ddc.json PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc etc/land.sh`
only on 81's go.

## Build command

`export TMPDIR=/shared/tmp; flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p
MemoryMax=64G python3 etc/timed-build.py --packages=/shared/tmp/manifest-ddc.json`
