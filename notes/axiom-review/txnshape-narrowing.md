# `Txn_CommitOn_dist` and `KV_DeleteOn_dist` take `kvShapeAll` (2026-11-27)

Branch `etcd-safe-txnshape/2026-11-27`, stacked on `etcd-safe-onpairs/2026-11-27` (`onpairs-deleteon.md`).
Two landed interim axioms are narrowed by a premise. That shrinks trust and adds no top-level premise, so the
coordinator pre-approved it.

## The finding (independent review, dsverify-net, 2026-11-27)

`Txn_CommitOn_dist` is sound for its success post, but its write arm over-claims the update:
- With auth on, Go refuses a transaction whose comparison or operation has an empty or inverted range
  (`permission denied`), and the entry still commits as a no-op.
- The model's `covers` is vacuous on such a range, so it grants the request, and `writeAuD`'s update
  (`kvAu1G`) applies its puts to the ghost KV state: the ghost state and the store diverge.
- Go's verdict on an inverted range also depends on the shape of the permission interval tree
  (`IntervalTree.Contains`): two users with the same permissions inserted in a different order get different
  verdicts.
- No exploit through a proved result was found.

Evidence: Go tests against the fork, `~/.claude-F/jobs/03d8018a/tmp/dsn/rev-shape/authshape/{adtt,srv}`
(`srv-auth.out`, `adt-contains.out`). The earlier review's "Noted" paragraph (`f7-txn-nested-review.md`), which
argued that `kvShapeAll` matters only for a refusal's content, is corrected there.

The in-process contract already requires it: `client.client_txn_on`'s `hsh` (`ResultsOn.lean:376`); the delete
contract's `etcdDeleteSpecOnW` requires `auth.reqShape` of the wire request (`KVServiceOn.lean:106`).

## The change

| axiom | Today | With this change |
|---|---|---|
| `Txn_CommitOn_dist` (`Spec/.../dist/TxnCommitOnDist.lean`) | write arm: `¬readonly ∧ (plain ∨ leased) ∧ txnNoZeroEnd ∧ txnNestOk` | the same `∧ ∀ tw, tw.toModel = txnWireOf b.model → kvShapeAll (irrTxn tw)` (= `client_txn_on`'s `hsh`) |
| `KV_DeleteOn_dist` (`Spec/.../dist/KVDeleteOnDist.lean`) | on lean: no shape premise; onpairs: `auth.reqShape key rangeEnd` (the caller's key) | both: `auth.reqShape key rangeEnd ∧ kvShapeAll (irrDeleteRange (deleteWireOf (opDeleteModel key opts)))` (the shape on the wire request, the transaction's vocabulary) |

**Why `KV_DeleteOn_dist` keeps both** (the coordinator's condition: replacing `reqShape` must not strengthen the
axiom). The new premise does not imply the old one from the axiom's pure premises (`¬ opDeletePanics`, `t = 3`,
`rangeEnd ≠ [W8 0]`): the options are arbitrary transformers `opts : List (OpFull → OpFull)` (`opFold`,
`client/v3/InvOp.lean:211`), constrained to Go's real options only by the Iris premise `optsAt`, so a pure lemma
cannot show the wire key is `key` (a transformer may replace an empty key by a non-empty one with a range end other
than `[0]`). With both premises the axiom only loses cases. (For Go's options, the key changes only with
`WithPrefix`/`WithFromKey` on an empty key, which set the range end `[0]`, excluded; so the two coincide in practice.)

The read-only arm is unchanged: it is a linearizable read whose `Q σ` is a read of the state, with no update.
(`KV_GetOn_dist`'s success is `readCheckedD`; a refused read claims nothing.)

## Callers

All discharge it without a new premise:
- `work_commitD` (`auth/WorkCallsDist.lean`) takes `hsh`; `Work.wp_proof_dist` passes `t1M_ok`/`t2M_ok`/`t3M_ok`'s
  (already computed for the in-process `akTxnOk`).
- T4 (`then_commit_nested_refusedD`): `t4M_shape` on the non-empty key `c/<who>/t3`.
- `RunAuthLease` (`dist/client/`): `leaseTxnD_shape` (new, `AuthLeaseTxn.lean`, the port of `authlease/run.lean`'s
  shape part) at the keys `a/txn`, `a/x`.
- `work_deleteD`: both from its `hk : k ≠ []` at `opts = []`.

The `dist-axiom-diff` pair with `client_txn_on` loses its `hsh` `dev` lines (the premise now lines up).
