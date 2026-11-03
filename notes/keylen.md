# The key-length law (2026-10-30/31)

The clients' model of etcd (`class EtcdModel`, `cache/v3/EtcdModel.lean`) has a law
`etcdState_keys`: every key of etcd's state, at every revision, is at most `etcdKeyMax = 2 ^ 27`
bytes. Clients that send a key they read from etcd (a recipe's queue key, a mutex's waiter key, a
leasing revocation) need it for the size premises of their requests (`opSizeOk`, `watchSizeOk`,
`notes/invoke-size.md`, `notes/invoke-size-b.md`). Approved by the user on 2026-10-30 (the
draft's Q0-Q8; `notes/decisions.md`, "The key-length law").

## Where the bound comes from

etcd's `processInternalRaftRequestOnce` refuses a request whose encoding is longer than
`Cfg.MaxRequestBytes` (`ErrRequestTooLarge`), before `r.Propose`: the only path a normal entry
takes into raft. Two facts make that a bound on the keys:

- **Trusted** (one conjunct of an axiom's post, commit `0d43bc2dd8`): `proto.MarshalIRR.spec`'s
  success branch gives `apply.irrKeysLe bs.length rq'`, every key the decoded request puts (its
  `Put`'s, its transaction's at any depth) at most the encoding's length. protobuf encodes a set
  `bytes` field as its tag, its length and all its bytes. The axiom keeps its name
  (`proto.MarshalIRR.wp_proof`), so `etc/tcb-report.py --check` does not see the change; it is to
  go through an axiom review (the `axiom` skill) before landing.
- **A scope restriction**: `NewServer` (its three statements) takes
  `v3rpc.etcdMaxRequestBytesOk (uint.nat cfg.MaxRequestBytes')` (`MaxRequestBytes + 512 KiB <
  2 ^ 27`, the premise the lock and election servers already use). The code accepts any limit;
  etcd's default (1.5 MiB) and the examples' meet it. It is kept in `srvReqFieldsAt` and its copies.

## The server side

- **Vocabulary** (pure): `mvcc.LogKeysLe n log` (`LogLemmas.lean`: every put of the log has a key
  of at most `n` bytes; `stateAt_keys`); `TxnOp.putKeysLe`, `TxnModel.putKeysLe`
  (`cache/v3/InvEtcdTxn.lean`); `apply.irrKeysLe` (`apply/InvRequest.lean`, over the request's
  model transaction `rq.txn`).
- **The invariant**: `kvWork`/`kvWorkOn` gain `logKeysOk L` (every normal entry with data of the
  committed log decodes to a request with short keys; `KVKeys.lean`) and
  `LogKeysLe etcdKeyMax γk.log0`. Kept by `kvWork_snoc`, from the proposal lemmas' new argument
  `hk : irrKeysLe etcdKeyMax rq` (`kv_prop_au`, `kv_prop_au_on`, `kv_prop_au_M`), which
  `wp_proofM` derives from the size check and MarshalIRR's conjunct. The boot entries are conf
  changes (the guard). `kvWorkC` (the compaction mode, no proposer) is unchanged.
- **The model**: `kvRaftOf_keys` (`KVKeys.lean`), `kvRaftOfOn_keys` (`ReadOn.lean`).
- **Reading it**: `srvKVCoreM_keys` (`ReadOn.lean`): with the KV core in either auth mode and a
  sealed log `B` of at least two revisions with short keys, every sealed certified log has short
  keys (`kv_cert_read(_on)`; a log of at most two revisions is a prefix of `B`). The read view's
  floor (`srvReadFieldsAt(M)`, `srvReadBuilt`, `InvBuild`'s view) gains `LogKeysLe` of its
  log, which `NewServer` proves of `[[], []]`; `readM_keys`/`read_keys` give a handler the bound of
  any log it read or wrote. (This is the draft's Q8, settled with no new premise.)

## The producers

- `kvLogOkTo` (the client KV specs' posts) gains `LogKeysLe` of the log through the revision;
  `kvLogOkTo_of_prefix`, `kvLogOk_of`, `kvLogOk_of_prefix` take it, `kvLogOk_keys` gives it.
- The KV reply predicates (`KVService.lean`: `putReplyOk`, `putReplied`, `rangeReplyOk`,
  `deleteReplyOk`, `deleteReplied`, `txnReplied`) gain `⌜LogKeysLe etcdKeyMax L⌝` beside
  `certOk E.γ L`, proved in the handlers (`client/v3/Results.lean`, `ServedOn.lean`) by
  `read_keys`/`readM_keys` (the draft's Q6: the registered specs get stronger).
- `srvLog` (and so `srvEtcdState`, `srvStep`), `kmLog`, `histLog` and `srvWL` gain the conjunct;
  `etcdState_of_sealed`/`_cert` and their `_last` forms take it.
- `watchLaws_srv` takes the member's `srvKVFacts` (its callers hold it); `histWL_of_sealed` takes
  the bound as an argument, which `watchLaws_hist` proves by `srvKVCoreM_keys`; `raw_to_state` the
  same.
- `v3rpc.etcdState_of_range` and `etcdState_of_txnRead` (exported, unused) take the server's read
  view and conclude under an update: the only statement change beyond the draft (it missed
  them); see the report.

## The clients

`etcdState_keys`, the three instances' proofs (`srvEtcdState_keys`, `kmEtcdState_keys`,
`histEtcdState_keys`). The callers: see `notes/STATUS.md`.

## Leasing's revocations (2026-10-31, the coordinator's authorization of an internal change)

`leasingKV.revokeLeaseKvs` gets the get of each data key it revokes to fit from a new premise,
`∀ v ∈ kvs, v.key.length ≤ etcdKeyMax`; `txnLeasing.revokeFallback` takes the same of every
response's key-values (`∀ kvs ∈ kvss, ...`). Both specs are internal to leasing, with no API
list. Their callers prove it from the response they got:

- `revokeRange`: from its get's `getRespRange` (`etcdState_keys` of the selected state and
  `rangeKvsOk_keys`, `InvLeasingKV.lean`: a sort, a limit, keys-only or count-only keep a bound on
  the selection's keys).
- `serverTxn`: `fallbackResps_ro` (`InvLeasingCommitLemmas.lean`) takes a bound on the keys of the
  fallback gets' selections and returns it of their key-values; the gets select from the
  transaction's state (`runOps_gets`, `runOps_gets_keys`), whose keys `txnStates` bounds through
  `etcdState_keys`.

No exported statement changes.

