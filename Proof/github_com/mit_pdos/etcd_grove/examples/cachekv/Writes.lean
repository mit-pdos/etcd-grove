/-
**The writers' vocabulary** (2026-10-20; over the KV state, D47, 2026-10-26). Lean-first (no Rocq
counterpart).

watchkv's (`Proof/.../watchkv/Writes.lean`): the KV state's half is in the adapter's invariant
(`client.kmInv γ`) at the plan's fact `γ.W = watchkv.wkW P`, which the cache's reads (its client
contract, `client.isEtcdClient_of_km`) and the writers' puts (the adapter's write update, in the
shared `common.Writer`; `watchkv.wk_put_W`) share; what the program knows of a successful Put
(`okFactKM`) and the log's lock invariant (`wsInvKM`) are the shared start's
(`common/WritesKM.lean`). (Until D47 the client's half was in `client.kvClientInv`, with the
cache's gets' updates from it, and the facts were of the server's sealed logs.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Writes
