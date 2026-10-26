/-
**The writers' vocabulary** (D23, 2026-10-20; over the KV state, D48, 2026-10-26). Lean-first (no
Rocq counterpart).

* The KV state's half is in the adapter's invariant (`client.kmInv γ`, `client/v3/EtcdModelKV.lean`)
  at the plan's fact `γ.W = wkW P` (`Workload.lean`): every change of the KV is a writer's put of
  the plan, the adapter's write update (`client.km_write_au`) at a put of the plan keeping it
  (`wk_put_W`). (Until D45 the server's workload restricted the log to the plan's puts, and the
  client's half was in an invariant of watchkv's own, `wkKV`.)
* What the program knows of a successful Put it logged, and the log's lock invariant: the shared
  start's (`common/WritesKM.lean`: `okFactKM`, `wsInvKM`, at the adapter's names).
* The Put itself is the shared `common.Writer` (`client.client_Put_rep`, D31).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WritesKM

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- **A writer's put keeps the plan's fact** (`common.Writer.spec`'s premise at `γ.W = wkW P`). -/
theorem wk_put_W (γ : client.KMNames) (P : List (GoString × GoString)) (hW : γ.W = wkW P) :
    ∀ k v, (k, v) ∈ P → ∀ σ : KVState, γ.W σ.changes →
      γ.W (kvOpStep (.put (client.putKeyOp k v)) σ).changes := by
  intro k v h σ hσ
  rw [hW] at hσ ⊢
  exact wkW_put P k v h σ hσ

/- What the program knows of a successful Put it logged, and the log's lock invariant: the shared
start's (`common/WritesKM.lean`). -/
export common (okFactKM okFactKM_persistent okFactKM_of_reply wsInvKM kmRevAt kmRevAt_agree)

end watchkv
end EtcdGrove
end Perennial
