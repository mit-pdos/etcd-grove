# The value-length law (2026-10-31)

The user's choice (2026-10-31), after pass 4 of the encoded-size bound left k8setcd3's no-op update
open (`notes/invoke-size.md`, "Pass 4"): the values of etcd's state get the key-length law
(`notes/keylen.md`), and `store.GuaranteedUpdate.spec`'s premise bounds only a written result.
Decisions: `notes/decisions.md`, "The value-length law", "GuaranteedUpdate's size premise".

## What changed

- `EtcdModel.etcdState_vals` (every value at most `etcdKeyMax`), with the instances
  `histEtcdState_vals`, `kmEtcdState_vals`, `srvEtcdState_vals`.
- Trusted, commit `f5c9aceb9a`: `proto.MarshalIRR.spec` gives `apply.irrPutsLe bs.length rq'`
  (keys and values of the request's puts) in place of `irrKeysLe`. Its axiom review is to be redone
  for the extension.
- The key vocabulary covers values, renamed: `TxnOp.putsLe`, `opsPutsLe`, `apply.irrPutsLe`,
  `mvcc.ChPutsLe`, `mvcc.LogPutsLe`, `logPutsOk`, `entryPutsOk`; new `mvcc.stateAt_vals`,
  `stateAfter_vals`, `applyChanges_vals`, `findKey_val_le`. An `IgnoreValue` put stores the old
  value, so `srvOp_keys`/`srvOps_keys` take the state's values' bound.
- `rangeReply_state_bnd`, linkvtxn's `txn_Commit_st`, `kubernetes.Client.Get.spec` and
  `Client.OptimisticPut.spec` give the state's values' bound (`etcdKeyMax`).
- The k8s store: `getStateOk`'s answer and `updateOnce`'s conflict carry it; `GuaranteedUpdate`'s
  loop keeps the bound of the value read; its premise is Go's write condition (stale, or the
  encoding differs) with the read value bounded.
- k8setcd3's no-op update closes by `decodeObjD_encode_length` (a re-encoding is as long as the
  data decoded).
