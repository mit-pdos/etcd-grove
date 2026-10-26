/-
**The writers' vocabulary** (2026-10-20; over the KV state, D48, 2026-10-26). Lean-first (no Rocq
counterpart).

watchkv's (`Proof/.../watchkv/Writes.lean`): the KV state's half is in the adapter's invariant
(`client.kmInv γ`) at the plan's fact `γ.W = watchkv.wkW P`, which the cache's reads (its client
contract, `client.isEtcdClient_of_km`) and the writers' puts (the adapter's write update, in the
shared `common.Writer`; `wk_put_W`) share; what the program knows of a successful Put
(`okFactKM`) and the log's lock invariant (`wsInvKM`) are the shared start's
(`common/WritesKM.lean`). (Until D48 the client's half was in `client.kvClientInv`, with the
cache's gets' updates from it, and the facts were of the server's sealed logs. Until 2026-10-26
watchkv's were the same, here from its `Writes.lean`; watchkv now has its own invariant.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WritesKM

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- **A writer's put keeps the plan's fact** (the adapter's write update's premise at
`γ.W = wkW P`). -/
theorem wk_put_W (γ : client.KMNames) (P : List (GoString × GoString)) (hW : γ.W = watchkv.wkW P) :
    ∀ k v, (k, v) ∈ P → ∀ σ : KVState, γ.W σ.changes →
      γ.W (kvOpStep (.put (client.putKeyOp k v)) σ).changes := by
  intro k v h σ hσ
  rw [hW] at hσ ⊢
  exact watchkv.wkW_put P k v h σ hσ

end cachekv
end EtcdGrove
end Perennial
