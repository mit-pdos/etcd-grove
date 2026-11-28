# nomode design X: the auth verdict as a function of the replicated state

Design X (decided 2026-11-27, `~/coordinator-notes/plans/nomode-packet.md`, "Decisions"): model etcd's
range-permission interval tree exactly, so that the permission cache, and the verdict on every range Go
accepts (inverted ones too, whose verdict depends on the tree's shape), is a function of the auth state.
Stages: X-a1 (the fork's sort, the model's role order), X-a2 (the exact tree in `pkg/v3/adt`), X-a3 (the
auth verdict over it), N1b (the request model without shape premises).

## X-a1: a role's permissions in one order

**Go (fork, local).** `permSlice.Less` compares `(Key, RangeEnd)` (`bytes.Compare` of the keys, then of the
range ends): branch `goose-lean-permsort` of the etcd fork, `18ab647b0` on `d26dd5da6`, with
`TestRoleGrantPermissionCanonicalOrder` (three grant orders, one record; fails before the change). Pushed
2026-11-27; the examples' Go modules (`examples/go.mod`, `examples/k8s/{etcd3,compactor,all,dist}/go.mod`)
name it (`v3.0.0-20261127200926-18ab647b0277`, X-a3). Why: same-key permissions kept grant-history order (`sort.Sort` is unstable, and stable on
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

## X-a3: the auth verdict over the exact trees

Go's verdict on a non-root user's request is now a function of the state for every request
(`notes/specs-only/ledger.md`, 2026-11-27, "the auth verdict as Go's"). New vocabulary (`auth/Model.lean`, moved
there from `PermTree.lean`: `permIvl`, `ivlsOf`, `queryIvl`):

- `permVal := interface.mkOk (go.GoType.StructType []) (LitV LitUnit)` (`struct{}{}` as `any`, the value inserted);
- `treeOf op ps := (ivlsOf op ps).foldl (fun T x => T.insertRB (x, permVal)) .leaf`: the tree `getMergedPerms`
  builds (`ivlsOf` keeps `ps`'s order: the user's roles as stored, each role's permissions as stored, sorted by
  X-a1; a point is `[k, k ++ "\x00")`, a `"\x00"` end the top `""`);
- `coversX st u op key rangeEnd : Bool := if rangeEnd = [] then decide (∃ x ∈ ivlsOf op (userPerms st u),
  adt.inIvl x key) else adt.containsT (queryIvl key rangeEnd) (treeOf op (userPerms st u))`
  (`checkKeyPoint`'s `Intersects`; `checkKeyInterval`'s `Contains` on the exact tree).

**Trusted-visible definitions: before / after.**

- `auth.granted st ai key rangeEnd op`. Before: `ai.rev ≠ 0 ∧ ∃ u, st.users !! ai.user = some u ∧ (isRoot u ∨
  (reqShape key rangeEnd → covers st u op key rangeEnd))`. After: `ai.rev ≠ 0 ∧ ∃ u, st.users !! ai.user = some u
  ∧ (isRoot u ∨ coversX st u op key rangeEnd = true)`. (Its signature gains `[GooseExts]`: `coversX` is over
  `adt.Entry`.)
- `auth.refusedV v ai key rangeEnd op`. Before: `v.flag.enabled = true ∧ (ai.rev = 0 ∨ ai.rev < v.rev.revision ∨
  ∀ u, v.user.users !! ai.user = some u → ¬ isRoot u ∧ (reqShape key rangeEnd → ∀ u', v.cache.users !! ai.user =
  some u' → ¬ covers v.cache u' op key rangeEnd))`. After: the last conjunct `∀ u', v.cache.users !! ai.user =
  some u' → coversX v.cache u' op key rangeEnd = false` (no guard). `refusedV_diag` loses its `reqShape` premise.
- `auth.cacheVerdictP sc user k e pt b` (moved from `Latest.lean` to `PermTree.lean`). Before: `k ≠ [] → (e = [] ∨
  isOpenEnded e ∨ go.GoStringLt k e) → permKeysOk sc → (b = true ↔ ∃ roles, sc.users !! user = some roles ∧ (if e
  = [] then coversPoint sc roles (permOp pt) k else coversRange sc roles (permOp pt) k e))`. After: `b = true ↔ ∃
  roles, sc.users !! user = some roles ∧ coversX sc roles (permOp pt) k e = true`.
- `auth.cacheVerdict M user k e pt b` (`InvAuth.lean`): its `on γa` body was `cacheVerdictP`'s text inline; now
  `∃ i sta, authStateAt γa i sta ∗ ⌜cacheVerdictP sta user k e pt b⌝`.
- `auth.permRefusalFrom` (`FreshCheck.lean`, `isWatchPermitted`'s refusal): the cache clause, before `(reqShape key
  rangeEnd → ∀ u', sc.users !! info.Username' = some u' → ¬ covers sc u' op key rangeEnd)`, after `∀ u',
  sc.users !! info.Username' = some u' → coversX sc u' op key rangeEnd = false`.
- `auth.permVerdictL` (`Latest.lean`, the apply thread's verdict): its `on` clause gains a third conjunct
  `permKeysOk stl` (the latest state's keys non-empty: the bridge to `covers` the KV model's `kvGranted` still uses
  needs it, `permVerdictL_granted`); `permVerdictL_iff` loses its `reqShape` premise.
- `auth.cacheEntryIs st u Tr Tw` (moved to `PermTree.lean`, untrusted). Before (lists): `∃ roles, st.users !! u =
  some roles ∧ (Lr.map Prod.fst).Perm (ivlsOf .read (userPerms st roles)) ∧ (Lw.map …).Perm (ivlsOf .write …)`.
  After (trees): `∃ roles, st.users !! u = some roles ∧ Tr = treeOf .read (userPerms st roles) ∧ Tw = treeOf
  .write (userPerms st roles)`. `permsAt p Tr Tw` holds `adt.ownIvtTB tr Tr .discard` (was `ownIvtB tr Lr`).

**Specs (untrusted).** `checkKeyInterval`: `b = adt.containsT (queryIvl k e) (if pt = W32 0 then Tr else Tw)`,
every query (was: the coverage, for a non-empty key and an open-ended or proper range). `checkKeyPoint`: over
`Tr.inorder`. `getMergedPerms`: text unchanged, its `cacheEntryIs` now the tree equality (the loop invariant is
`Tr = treeOf .read (userPerms st (take n roles) ++ …)`, `treeOf_snoc`). adt: `Insert_bytes` and `Contains_bytes`
on `ownIvtTB` (`ownIvtT bytesKey`), results `T.insertRB ((bs, es), v)` and `r = containsT (bs, es) T` (no
premise); pure `RbCtx.inorder_fixup`, `RbT.inorder_insertAt`, `RbT.inorder_insertRB` (`TreeInsert.lean`).

**Bridges** (`PermTree.lean`): `coversX_iff_covers` (`permKeysOk`, `reqShape`: `coversX = covers`),
`granted_iff_covers` (the old `granted` form; used by `WatchClass`, the auth example's `Model`/`WorkAuth`, and
`AuthLeaseRefusalFacts`, which take `permKeysOk` from `authStateAt_permKeysOk` or `setupSt_permKeysOk`),
`coversX_emptyKey` (an empty key: `false`, every range end), `coversX_point_of_not_lt` (an empty `[k, k)` or
inverted range granted ⇒ `coversPoint k`). Not proved: `[k, k)` ⇐ `coversPoint k`; it needs every stored
permission's range valid (`rangeValid`, which `RoleGrantPermission` checks but no state invariant states), since
`Visit`'s pruning at a node with an empty interval `[b, e)`, `e ≤ b`, would miss it.

**Statements.** No top-level statement's text changes; `authkv_granted_iff` (`examples/etcd/auth/Results.lean`)
gains a `[GooseExts]` binder (it names `auth.granted`). Its meaning at the point requests it states is unchanged
(`granted_iff_covers`).
