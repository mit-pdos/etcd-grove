# A depth premise for `proto.MarshalIRR`, discharged from a `MaxTxnOps` bound (2026-10-31, branch `irr-depth`)

The repair of `proto.MarshalIRR.wp_proof`, which the axiom review `axiom/txn-nested-wire` (attack 9)
found false: it claimed that the encoding of *any* `InternalRaftRequest` decodes, and one whose
transaction is 10000 messages deep does not (protobuf-go's recursion limit), so
`pbutil.MustUnmarshalMessage` panics at apply, on every member, again on replay
(`issues/etcd-txn-nested-depth-apply-panic.md`). The design (the draft's C1-C14, reviewed twice) was
approved by the user on 2026-10-31 with all seven of its recommendations; it is recorded in
`notes/decisions.md`, "A depth premise for `proto.MarshalIRR`". This file records the change as
built.

## State: done (statements as approved, all proved; no new axiom, no new `sorry`)

## What changed, by layer

- **The trusted statement** (`Spec/google_golang_org/protobuf/proto/MarshalIRR.lean`): the premise
  `apply.irrDepthOk rq →`, the post unchanged (`irrPutsLe` stays). The file header gains "The
  depth": protobuf-go's accounting at the pin (`proto/decode.go:61-63`, `internal/impl/decode.go:105`,
  `encoding/protowire/wire.go:28,113`), why only the transaction recurses, and the margin (the code
  also returns bytes for a deeper request, which do not decode). The axiom keeps its name, so
  `etc/tcb-report.py --check` does not see the change: it is recorded in `notes/audit.md` and the
  review `notes/axiom-review/marshalirr-depth.md`.
- **The vocabulary** (`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/IrrDepth.lean`, new; not in
  `cache/v3/InvEtcdTxn.lean`, so the cache does not rebuild): `apply.protoRecursionLimit` (10000),
  `apply.depthMax`, `TxnOp.msgDepth`, `TxnModel.msgDepth`, `apply.txnDepthOk`, `apply.irrDepthOk`;
  the laws `apply.irrDepthOk_of_txn_none`, `_of_txnW_none`, `apply.txnDepthOk_mono`,
  `apply.depthMax_le`, `apply.txn_none_of_dispatchKind` (a kind `dispatch` tests after `.txn` has no
  transaction). Beside their subjects: `apply.irrDepthOk_withHeader` (`MarshalIRR.lean`, `Iff.rfl`),
  `apply.irrDepthOk_irrTxn` (`InvProposer.lean`), `irrDepthOk_of_adminRespTy` (`AdminOn.lean`),
  `irrDepthOk_of_compactPropOk` (`CompactMode.lean`).
- **The server's proposer**: `processInternalRaftRequestOnce.spec`, `raftRequest.spec`, their
  `specM`/`specOff` (`ModeSpecs.lean`) take `apply.irrDepthOk rq →` after `rq.id = W64 0 →`.
  `specCompact` is unchanged (its proof, a `sorry`, would use `irrDepthOk_of_compactPropOk`). The
  callers: `Put`, `DeleteRange` (`irrDepthOk_of_txnW_none rfl`, both modes), `authnRaft_on` (the
  same), `authRaftOk_on` (`irrDepthOk_of_adminRespTy hT`, its statement unchanged), `Txn`
  (`irrDepthOk_irrTxn`).
- **`EtcdServer.Txn`**: `spec` takes `⌜txn.txnReadonly t = false → apply.txnDepthOk t⌝` (a read-only
  transaction is not proposed); `specOn` takes `⌜txn.txnReadonly t = false ∧ apply.txnDepthOk t⌝`;
  `specOnR` unchanged. `txn_applied` (exported) takes `(hd : apply.txnDepthOk t)`; `txn_readonly`
  unchanged.
- **v3rpc**: `v3rpc.maxTxnOpsOk (n : Int) : Prop := n ≤ 4999` and `maxTxnOpsOk_default` (`RecvLimit.lean`,
  beside `etcdMaxRequestBytesOk`); the one real proof, `v3rpc.txnCheck_msgDepth` (a transaction
  `checkTxnRequest` accepts at budget `n` is at most `2n + 1` deep, by the mutual
  `opCheck_msgDepth`/`opsCheck_msgDepth`), with `txnDepthOk_of_check` and `txnModelDepthOk_of_check`
  (`CheckLemmas.lean`). The contract `kvTxnOk` takes `∀ t, txnModelOf cs ts es = some t →
  apply.txnDepthOk t` (`txnModelOf` moved from `ServerKV.lean` to `InvKV.lean`). `kvServerIs` and
  `kvServerAt` keep `⌜maxTxnOpsOk (sint.Z n)⌝`; `NewKVServer.spec` and `NewQuotaKVServer.spec` take
  it as a premise; `grpcCfgOk` carries it to `v3rpc.Server`'s proof.
- **The configuration premise** (the scope restriction): `NewServer.spec`, `specCompact`, `specM` take
  `v3rpc.maxTxnOpsOk (sint.Z cfg.MaxTxnOps') →` after `etcdMaxRequestBytesOk`; `srvServeCfg`
  carries it to `grpcCfgOk_of_started`, `_w`, `_on_w` (statements unchanged). The examples
  (`MaxTxnOps: 128`) discharge it by `maxTxnOpsOk_default` (`common/newServer.lean` twice,
  `authkv/startServer.lean`).

## Departures from the draft

None in a statement. Internal choices:

- `apply.txn_none_of_dispatchKind` (`IrrDepth.lean`) is the shared step of the two laws
  `irrDepthOk_of_adminRespTy` and `irrDepthOk_of_compactPropOk` (the draft gave only their
  statements); `apply.irrDepthOk_of_txn_none` and `apply.depthMax_le` likewise.
- `v3rpc.txnModelDepthOk_of_check` (`CheckLemmas.lean`): `kvServer.Txn`'s discharge of `kvTxnOk`'s
  depth conjunct in one step (the draft: `txnDepthOk_of_check` with `txnModelOf_of_check`, which is
  in `ServerKV.lean`, not imported by the proof); the proof file `kvServer__Txn.lean` imports
  `CheckLemmas`, as `checkTxnRequest.lean`'s does.
- `NewKVServer`'s spec reaches `RecvLimit`/`IrrDepth` through `InvKV` (no import of its own).

## Checks (2026-10-31, at `2e8babd9bc`)

- `lake build` (full): green.
- `etc/tcb-report.py --check`: the baseline unchanged (769 axioms, 18 `sorry`s); the 43 collections
  `--check`: all pass, none updated (the axiom keeps its name; its restatement is recorded here, in
  `notes/audit.md` and in the review).
- `etc/api-check.py etc/api/raft.txt --check`, `etc/gen-interface.py etc/api/raft.txt --check
  --layout` (no interface moved: raft is the only package with an API list), `etc/gen-init.py
  --check`, `etc/gen-link.py` for the server, v3rpc, apply and client (identical).
- The axiom review of the restatement: survives (`notes/axiom-review/marshalirr-depth.md`).
