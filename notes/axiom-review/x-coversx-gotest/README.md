# X witness: the auth model's verdict against the real auth store (review rev-x4, 2026-11-28)

`zz_coversx_test.go.txt` drives etcd's real `authStore` (over the real bbolt backend) with random
admin operations and compares it with a literal Go transcription of the Lean model at nomode-x
`ebb6d80a07`: the adt tree (`RbT.insertAt`/`insertRB`, `RbCtx.fixup`, `visitL`, `containsT`) and the
auth model (`permKind`, `Perm.grants`, `treeOf`, `coversX`, `granted`, `rangeValid`, `grantPerms`,
the admin steps including `roleRevokePermissionR`). After every operation it compares the error,
revision and enabled flag; at the end every role record and user; then 400 READ and WRITE queries
per seed over point, proper, from-key, empty `[k,k)`, empty-key and inverted ranges, again after
`Recover`.

Run: copy it to `server/storage/schema/zz_coversx_test.go` in a checkout of the pinned fork
(upamanyus/etcd `18ab647b02`), then `CX_SEEDS=20000 go test ./storage/schema -run TestCoversXDifferential`
(go1.27.3).

Result of the review run: 20,000 seeds, 16,000,000 queries, 0 mismatches (verdicts, records,
revisions, errors); 830k inverted and 3.7M empty `[k,k)` queries, 60k grants on inverted or empty
ranges, 16k stored unknown-type permissions.

Mutation check (each a manual edit of the transcription, 1,000 seeds each): insert without the
red-black fixup (many mismatches, all inverted ranges), visit as a plain overlap filter (71), an
unknown type granting read (2,410), point queries answered through the tree (1,113).
