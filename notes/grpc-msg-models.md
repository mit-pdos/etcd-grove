---
title: grpc's ProtoMsg/StreamMsg axioms take caller-built message models
found: 2026-11-07
by: axiom sweep, the "trusted model as a parameter" pass (etcd-grove-c9)
blocks-proof: yes
status: open; the fix joins the per-type stage of notes/pbenc-ok-inconsistent.md
---
# grpc's `ProtoMsg`/`StreamMsg` axioms take caller-built message models

This is a bug in our trust base, not in grpc or etcd. It is written in the shape of a non-issue.

Four axioms quantify over a record whose fields are the trusted wire model of a message type:
`grpc.serve` and `grpc.ClientConn.Invoke.wp_proof`, over `ProtoMsg`, and `grpc.serveStream` and
`grpc.ClientConn.NewStream.wp_proof`, over `StreamMsg`. Nothing ties a record to its Go type or the
sender's `send` to the receiver's `recv`. So a program that runs its own server and its own client
can choose a reply model whose `recv` is `False`. The client is then proved never to receive a reply
that grpc-go delivers, and a program that panics when the reply arrives is proved safe. This holds
for unary calls (`axiom/protomsg`, `8d7ff9b9b4`) and for streams (`axiom/streammsg`, `f285e9d4aa`).
`notes/axiom-review/grpc-msg.md` gives the theorems and their `#print axioms`.

**Why not an issue:** the bug is in our trust base. grpc-go delivers the message; the axioms state
its model at a quantifier that no Go fact supports.

## Proof

yes: every result whose `#print axioms` lists one of the four rests on a refuted axiom until the fix
lands.

From `.lake/tcb.json` at `lean` `158829a8b9`: 207 of the 4898 linked results list one of the four
axioms, and so do 59 of the 881 exported results.

**The 17 `*_safe` results** (the same as for `pbEnc_ok`):

- `etcd_cache_safe`, `etcd_compacted_safe`, `etcd_compactwatch_safe`;
- `etcd_lease_safe`, `etcd_leasecatchup_safe`, `etcd_leaseexpiry_safe`, `etcd_leasegrant_safe`;
- `etcd_partition_safe`, `etcd_partition_watch_safe`;
- `etcd_putget_safe`, `etcd_putget3_safe`, `etcd_txnlin_safe`, `etcd_watch_safe`;
- `k8s_compactor_safe`, `k8s_compactor_partition_safe`;
- `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`.

**The other 42 exported results:**

- the examples' entry points:
  - `authkv_SetUp`, `cachekv_Main`, `putgetc_Main`, `compactkv_Main`;
  - `leasekv_Main`, `leasecatchup_Main`, `leaseexpiry_Main`, `leasegrant_Main`;
  - `linkv3p_Main`, `linkv3p_MainWatch`;
  - `putget_Main`, `putget3_Main`, `linkvtxn_Main`, `watchkv_Main`;
  - `k8s_compactor_Main`, `k8s_compactor_MainPartition`;
  - `k8setcd3_Main`, `k8setcd3_MainCluster`;
- the cache: `cache_end_to_end_client`, `cache_end_to_end_new`, `etcd_cache_served`;
- clientv3:
  - `kv.wp_Compact`, `kv.wp_Delete`, `kv.wp_Get`, `kv.wp_Put`, `txn.wp_Commit`;
  - `client_delete_end_to_end`, `client_get_after_put`, `client_put_end_to_end`,
    `client_txn_end_to_end`;
  - `client_lessor_isEtcdLease_served`, `client_new_isEtcdLeaseClient_served`;
  - `client_watcher_progressNotifier`, `etcd_kv_lease_served`, `etcd_kv_served`,
    `watchClient_Watch`;
- the recipes: `recipes_client_of_km`, `recipes_kv_of_km`;
- v3rpc: `etcd_auth_served`, `etcd_watch_served_etcd_chain`;
- k8s: `k8s.store.wp_GetCurrentResourceVersion`.

Every exported result that lists `pbEnc_ok` also lists one of these four axioms.

## Notes

The fix, as the user decided via etcd-grove-82 on 2026-11-07, is the per-type stage of
`notes/pbenc-ok-inconsistent.md`:

- fixed instances of the message models;
- satisfiable `recv`, `send` and `wireLen`;
- the axioms over those instances only;
- the gate covering `ProtoMsg` and `StreamMsg`.

The sweep's clearances of other record-quantified axioms are in
`notes/axiom-review/model-param-sweep.md`.
