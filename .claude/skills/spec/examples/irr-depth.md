# A depth premise for `proto.MarshalIRR` (2026-10-31)

A trust-boundary axiom found false at an input its callers can produce: `proto.MarshalIRR` claimed
that the encoding of any `InternalRaftRequest` decodes, and protobuf-go refuses one more than 10000
messages deep (`issues/etcd-txn-nested-depth-apply-panic.md`: a 4999-deep nested transaction passes
gRPC and panics every member's apply). The repair restates the axiom with a premise and carries the
premise up to a configuration bound, through the server, the gRPC handler and `NewServer`. Drafted,
reviewed twice, then approved with all seven of the draft's recommendations (`notes/irr-depth.md`,
`notes/decisions.md`, "A depth premise for `proto.MarshalIRR`").

## The first version (round 0)

- The axiom takes `irrDepthOk rq` (the request's transaction at most 9999 messages deep), its post
  unchanged; the alternative, a weakened post (bytes always, their decoding only under the bound),
  was called "stronger, but claims what no caller uses".
- The server's proposer takes the same premise; `EtcdServer.Txn` a depth premise of a writing `t`.
- v3rpc: `maxTxnOpsOk n := n ≤ 4999` in `v3rpc/Defs.lean`; the handler's contract `kvTxnOk` gains
  `maxTxnOpsOk n` beside the check at the budget `n`; the `*kvServer` keeps the bound.
- `NewServer` takes the configuration premise.

## The critiques, and what each changed

1. **Round 1** (the first review): the admin requests' contract `authRaftOk_on` has an abstract
   request, so the caller's discharge needed a law over `dispatchKind`; `maxTxnOpsOk` moved to
   `RecvLimit.lean` (the server imports only that minimal v3rpc module: `Defs` would pull about 30
   modules into its closure); the issue file lands with the change; the list of exported statements
   that change was incomplete (`server_process_irr_on`, `server_raft_request_on`); the gRPC side's
   decoding was checked (etcd's own codec, the same limit); the reviewer's alternative contract over
   the depth recorded.
2. **Round 2** (the re-review):
   - **The contract over the receiver's need, not the supplier's mechanism**: `kvTxnOk` takes the
     depth of the request's model (`∀ t, txnModelOf … = some t → txnDepthOk t`), not the budget
     bound. The budget form implies it, not conversely (a flat transaction of 5000 comparisons
     checks only at `n ≥ 5000` and is 3 deep), so the server's spec is stronger and names no v3rpc
     budget.
   - Round 1's new kind `ReqKind.afterTxn` replaced by two direct laws (no new vocabulary).
   - The (P)/(W) paragraph corrected: the weakened post is not merely unused, it is false too: it
     claims `Marshal` returns at any depth, and Go's stack (a recursion per level) does not give
     that; the old axiom's claim there was false as well.
   - Two more exported statements found (`server_txn_on`, `v3rpc.wp_NewKVServer`).

## The approved spec

```lean
abbrev proto.MarshalIRR.spec : Prop :=
  ∀ (p : Loc) (rq : apply.IRRModel),
  apply.irrDepthOk rq →
  {{ isPkgInit pkg_id.google_golang_org.protobuf.proto ∗ apply.internalRaftRequestIs p rq }}
    proto.Marshal #p
  {{ (d : GoSlice) (err : GoInterface), RET (d, err);
      (⌜err = nil⌝ ∗ ∃ bs rq', d ↦* bs ∗ ownSliceCap d 1 ∗
        ⌜apply.irrDecode bs = some rq' ∧ irrWireOf rq rq' ∧ (rq.header ≠ none → bs ≠ []) ∧
          apply.irrPutsLe bs.length rq'⌝) ∨
      (⌜err ≠ nil⌝ ∗ applyErrIs err) }}
```

with `apply.irrDepthOk rq := ∀ t, rq.txn = some t → t.msgDepth + 1 ≤ 10000`, the proposer's and
`Txn`'s matching premises, the exact configuration bound `v3rpc.maxTxnOpsOk (sint.Z
cfg.MaxTxnOps')` on `NewServer` (`n ≤ 4999`: at 5000 the issue's chain passes the check), kept in
the `*kvServer` object, and the one real proof `v3rpc.txnCheck_msgDepth` (a transaction checked at
budget `n` is at most `2n + 1` deep) linking the two.

## What it shows

- **Repair a false axiom with a premise, not a post that claims more**: the weaker-looking premise
  form is the true one when the "stronger" post asserts termination Go does not give.
- **A contract between packages states what the receiver needs**, not how the supplier happens to
  establish it (the depth, not the budget); the supplier proves the law linking the two.
- **A configuration premise exactly as strict as the code**: the threshold computed from the check
  (`2n + 2 ≤ 10000`), shown tight, the default shown to meet it.
- **Keep a fact in the object that copied it** (`kvServerIs`), so the statements above it do not
  each carry a hypothesis.
