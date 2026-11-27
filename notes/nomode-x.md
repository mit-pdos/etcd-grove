# nomode design X: the auth verdict as a function of the replicated state

Design X (decided 2026-11-27, `~/coordinator-notes/plans/nomode-packet.md`, "Decisions"): model etcd's
range-permission interval tree exactly, so that the permission cache, and the verdict on every range Go
accepts (inverted ones too, whose verdict depends on the tree's shape), is a function of the auth state.
Stages: X-a1 (the fork's sort, the model's role order), X-a2 (the exact tree in `pkg/v3/adt`), X-a3 (the
auth verdict over it), N1b (the request model without shape premises).

## X-a1: a role's permissions in one order

**Go (fork, local).** `permSlice.Less` compares `(Key, RangeEnd)` (`bytes.Compare` of the keys, then of the
range ends): branch `goose-lean-permsort` of the etcd fork, `18ab647b0` on `d26dd5da6`, with
`TestRoleGrantPermissionCanonicalOrder` (three grant orders, one record; fails before the change). Local only
(the user pushes forks): `etc/goose.py --check` fails until it is pushed (and `examples/go.mod` still names
`d26dd5da6`). Why: same-key permissions kept grant-history order (`sort.Sort` is unstable, and stable on
short slices), so the record, and the cache's tree built from it, depended on history
(`issues/etcd-auth-perm-order-go-version.md`).

**Model: before / after** (the trusted-visible definitions; `notes/specs-only/ledger.md`, 2026-11-27).

- `auth.grantPerms ps w` (`Steps.lean`). Before: `ps.filter (¬ permAt w.key w.rangeEnd ·) ++ (permOfWire w).toList`
  (appended). After: the same filter, with `permOfWire w`'s permission inserted at its place by `permLt`
  (`permInsert`: before the first permission it is below); without a known type, the filter alone.
- `auth.rangeLt k e k' e'`, `auth.permLt p q` (`Model.lean`, new): `GoStringLt k k' ∨ (k = k' ∧ GoStringLt e e')`,
  `permSlice.Less`'s order.
- `auth.roleOut`/`roleOutX` (`Buckets.lean`). Before: `rr.name = name ∧ rr.toRole.Perm ps`. After:
  `rr.name = name ∧ rr.toRole = ps ∧ ps.Pairwise permLt`.
- `authBatchTxLk`'s `UnsafePutRole` premise (`InvAuth.lean`, both copies). Before: `rr.toRole.Perm ps`. After:
  `rr.toRole = ps ∧ ps.Pairwise permLt`.
- `schema.rolesAt`, `schema.authBucketsAre`'s roles clause (`InvAuthBackend.lean`). Before:
  `… ∧ rr.toRole.Perm ps`. After: `… ∧ rr.toRole = ps ∧ ps.Pairwise permLt`.
- `auth.roleGetOut` (`Reads.lean`). Before: `({ name, perms := ws } : RoleRec).toRole.Perm ps`. After: `… = ps`.

**Where the order invariant lives.** On the records (the reads' `roleOut`, the bucket invariant `rolesAt`), as
the users' sorted roles already are, not in the history's `permKeysOk`: the grant proof is generic in the
contract's mode, and in the mode `any` the history gives nothing, while the record read under the batch lock
always does. The proof: `grant_kept_eq` (`GrantPermLemmas.lean`): the sorted record's model role is a
permutation of the kept permissions with the new one, strictly sorted (distinct ranges, `sort.Sort`'s
postcondition), and so is `grantPerms ps w` (`grantPerms_sorted`); two such lists are equal
(`List.Perm.eq_of_pairwise`).

## X-a2: the interval tree, exactly

The tree's specs (`pkg/v3/adt`) now state the red-black tree itself, not only its entries, and
`visit`'s descent for every query (`notes/specs-only/ledger.md`, 2026-11-27). Untrusted (proved code);
before/after of the vocabulary:

- `adt.ownIvtT K t T dq` (`Defs.lean`, new): the tree at `t` is exactly `T` (with `RbOk T`, `IvSorted T.inorder`,
  the count). `ownIvtK` is unchanged; `ownIvtK K t L dq ⊣⊢ ∃ T, ownIvtT K t T dq ∗ ⌜T.inorder = L⌝`
  (`ownIvtK_T`, `ownIvtT_K`); `ownIvtK K t [] dq ⊢ ownIvtT K t .leaf dq` (`ownIvtK_nil`: `NewIntervalTree`'s
  spec unchanged gives `T = .leaf`).
- `adt.RbCtx.fixup C t`, `adt.RbT.insertAt z C T`, `adt.RbT.insertRB z T` (`TreeInsert.lean`, new): `insertFixup`'s
  loop and `Insert` as functions, mirroring the Go code's cases and colour writes.
- `adt.containsT q T` (`Contains.lean`, new): `containsRes`'s scan over `T.visitL q`; `containsT_eq`: equal to
  `containsRes q T.inorder` for a sorted tree and a query that is not empty-and-finite.
- Specs: `insertFixup` adds `T = C.fixup tz`; `Insert_gen` on `ownIvtT`, result `T.insertRB z` (and its entries
  `ivtInsert z T.inorder`); `visit`/`Visit_gen` (no query premise, no `IvSorted`): the visited entries are
  `T.visitL q` when no visitor stopped, a non-empty prefix else; `Contains_gen`: `r = containsT q T`.
  The entry-level forms are derived (`VisitL.lean`: `Visit_gen_L`, `Insert_gen_L`), so the string- and
  bytes-affine instance specs and every client are unchanged. X-a3 states the auth cache over `ownIvtT`
  (bytes-affine `Insert`/`Contains` at the tree level: through the `_gen` specs with `bytesKey`).
