# Lease-keeping puts in transactions (item 4 of the lessor/auth list, 2026-11-01)

Spec-first, as `notes/lease-read-plan.md`. Branch `lease-txnput`. The gap, from
`notes/lease-keys-plan.md` (Part A's `opLeaseClass`, review F4): `putKeep` and a lease-keeping
`putIgnVal` have the lease class `True`, because `TxnOp` forgets their wire `Lease`.

## Scope (2026-11-01)

**What Go does** (`server/etcdserver/apply/auth.go`, `txn/put.go`, `api/v3rpc/key.go` at the pin):
- `checkTxnReqsPermission` runs `checkPutAuth` on every put of the transaction, which runs
  `checkLeasePuts(r.Lease)`, the wire `Lease` field, `IgnoreLease` or not (`auth.go:78`, `157`).
- A put with `IgnoreLease` attaches the key's previous lease, not `r.Lease`
  (`txn/put.go:57-58`, `leaseID = prevKV.KVs[0].Lease`). The wire `Lease` is never attached.
- The gRPC layer rejects `IgnoreLease` with `Lease != 0` (`key.go:189`, `ErrGRPCLeaseProvided`),
  for a transaction's puts too. So on every request that reaches the apply layer through gRPC,
  a lease-keeping put's wire `Lease` is `0`. `Lookup(0)` finds no lease, because `Grant` refuses
  `NoLease` (`lessor.go:282`), and the check passes.

**So the gap is not a lost guarantee.** Read as "every lease the request attaches has keys the user
may write", the class is already complete. A lease-keeping put attaches no new lease: it keeps the
key's lease, and the key's own write is checked (`IsPutPermitted(key)`, `opClass`). The only thing
`True` leaves out is Go's check of the wire field, a lease the put does not attach, and that field
is `0` once gRPC has validated the request.

**Options**
- **A.** Reclassify: correct the docstrings (`opLeaseClass`, `AuthClass.lean`'s header, the
  lease-keys plan's gap, STATUS) to say why `True` is complete. No statement changes. Then item 5.
- **B.** State Go's check exactly: a wire-level lease class over `TxnOpW` (`o.leaseID` of every put,
  `IgnoreLease` or not), with the walk's specs taking `TxnModelW` where they take `TxnModel`.
  Faithful to the code, but the statement is about a lease the put does not attach, and it means
  re-plumbing the walk's specs, the chain and `Results.lean`'s `chain_txn`.

**The user's choice (2026-11-01): A.** The docstrings are corrected (`AuthClass.lean`'s header and
`opLeaseClass`, STATUS's lease-keys gaps, a note in `notes/lease-keys-plan.md`). No statement
changes. Next: item 5.
