# The `axiom-tok` gate on the 14 F7 auth axioms (F7 S3 step 4, 2026-11-26)

Branch `etcd-safe-f7` (the step-2 commit `c1328f9156`), fk-lean2. **No allow entry is added here** (for the lead /
coordinator).

**How it was run.** No root reaches the 14 axioms yet (`RunAuthLease` is not linked: `notes/etcd-dist-f7.md`,
"Handoff S3-1"), so `etc/axiom-tok-check.py`, which walks the axioms of `.lake/tcb.json`, would not see them. The
gate's own Lean walk (`etc/AxiomTokCheck.lean`, default depth, `proof_roots.lean_args()`) was run directly on the 14
`Proof/.../dist/<F>Dist.lean` modules with the 14 names, and judged by the script's `judge`/`report` against
`etc/axiom-tok-allow.txt` (a 30-line driver importing `etc/axiom-tok-check.py`; memory cap 55G). Result:
**14 walked, 0 pass, 14 need an entry, 14 truncated** (none collapsed by the scenario cap).

## Findings, by rule

| axiom(s) | rule 2 (`levelTok 0`) | rule 3 | rule 5 | rule 7 |
|---|---|---|---|---|
| `KV_PutOn`, `KV_DeleteOn`, `Auth_UserAdd`, `Auth_UserGrantRole`, `Auth_RoleAdd`, `Auth_RoleGrantPermission`, `Auth_AuthEnable`, `Lease_GrantOn`, `Lease_RevokeOn`, `Lease_TimeToLiveKeysOn`, `Lease_LeasesOn` (11) | handed to a callback 8, supplied directly 1 | none | none (they are the taint's sources, below) | `∃ P : IProp GF` (in `context.isCancelCtxOf`) |
| `Txn_CommitOn_dist` | handed to a callback **10**, supplied directly 1 | none | none | `∃ P` |
| `KV_GetOn_dist` | handed to a callback 8, supplied directly 1 | **atom `Q`: produced 1, consumed 0** | none | `∃ P` |
| `New_user_dist` | none | none | **yes**: through `grpcConn`, `metadata.builtRawMDRaw`, `status.statusAtRaw` | `∃ P`, and `∃ scd : context.ContextDesc` (in `context.isContextDone`, producing `scd.PDone` three times) |

Tainted opaque predicates (rule 5): `grpcConn`, `metadata.builtRawMDRaw`, `status.statusAtRaw`; their roots are the
11 axioms of the first row and `KV_DeleteOn`/the admin calls (the report lists six of them per predicate).

**Truncations (all 14):** `stuck projection: cd.4`, `depth: Perennial.named`, `stuck projection: Req.toProtoMsg.4 inp
m`, `Rep.toProtoMsg.{6,8,9}`, `depth: sync.isMutex`, `context.isCancelCtx{,Of}`, `isChan`, `status.statusAt`; 13 of
them also `stuck: Perennial.dghostVar` (all but `New_user_dist`). `--check` would fail on each without a `trunc` line.

## Reading (not a verdict)

- **Rule 2, 8/1:** exactly `Client_Put_dist`/`Client_Get_dist`'s accepted key `2:L:0:handedtoacallback8/supplieddirectly1`
  (`etc/axiom-tok-allow.txt`, "putget-dist's interim client axioms"): the caller's one `levelTok 0`, lent to the call's
  interceptor through the four connection contracts `isNewClient` carries and given back. All 14 take `levelTok 0` in the
  pre and return it in the post. **`Txn_CommitOn_dist`'s 10** is two more: `txnObjAt` adds a connection contract (the
  transaction's own `kvObjAt`/interceptor), to check against `Txn_Commit_dist`'s count.
- **Rule 7, `∃ P`:** the same `*cancelCtx` Done proposition as the accepted `7:P:IPropGF`.
- **`KV_GetOn_dist`'s rule 3 (`Q` produced 1, consumed 0):** the post's `□ Q σ` against the pre's
  `□ (⌜Q = fun _ => True⌝ ∨ AU … COMM □ Q σ)`: the walk does not see the `⌜Q = True⌝` arm as consuming. The same
  shape as `KV_Get_dist` (auth off), whose finding should be compared before an entry.
- **`New_user_dist`'s rule 5 and `∃ scd`:** the `New` shape (`grpcConn` consumed 4, produced 1; a context made inside
  `New`'s `getToken`), as for the existing `newClient`/`grpc.NewClient` axioms; not traced further.

Raw output: fk-lean2 `~/eg/logs/atok14.out` (and `.raw.jsonl`).
