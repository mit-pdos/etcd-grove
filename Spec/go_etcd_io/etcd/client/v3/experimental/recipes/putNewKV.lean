/-
`recipe.putNewKV(kv, key, val, leaseID)` (`key.go`): create `key` with `val` and the lease, only if it
does not exist (`If(Version(key) = 0)`).

**Users**: `newKV` (so `newKey`, `newEphemeralKV`, `Barrier.Hold`), `newUniqueKV` (`Queue.Enqueue`).
Snippet: `recipes/barrier.go` (`ReqHoldTwice`, through `Hold`).

**Proof sketch**: as `deleteRevKey`'s: `kv.Txn(context.TODO())`, `Compare(Version(key), "=", 0)` (an
untyped `0`: `CmpArg.int`, the comparison of `putNewReq`), `OpPut(key, val, WithLease(leaseID))`
(W0's `OpPut.spec`, `WithLease.spec`: the put of `putReq0`), `If`/`Then`/`Commit` (at `lo = 0`) with the caller's
update. `Commit`'s `txnReply`: `Succeeded` and the header's revision (`txnRespOwn_unfold`,
`respHeaderOwn_unfold`), `ErrKeyExists` read from its global (`init.spec`) when the comparison failed.

**Changes**: old spec required lease `0` or a session's lease named by its invariant, a prefix and
size bounds, and gave `keyCreatedAt`; now any lease (a lease not live is `ErrLeaseNotFound`, a
linearized answer), any key, the caller's update in W0's shape.

Changes: verify-round: `ErrKeyExists` is the value its variable holds (`putNewRetAt`), not a Lean constant (A3 F4).

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Recipes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.client.v3.experimental.recipes

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`putNewKV(kv, key, val, lease)`**: the transaction `putNewReq key val lease`, linearized by the caller's update; returns the revision it created the key at, or `ErrKeyExists`, or etcd's error. -/
def putNewKV.spec : Prop :=
  ∀ (kv : GoInterface) (γ : Cluster) (who : Principal) (key val : GoString) (lease : w64)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ kvAt kv γ who ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (putNewReq key val (sint.Z lease)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.putNewKV)) (Val #kv))
      (Val #key)) (Val #val)) (Val #lease))
  {{ (rev : w64) (err : GoInterface), RET (PairV #rev #err);
      (∃ σ σ' res, Q σ σ' res ∗ putNewRetAt res rev err) ∨ (⌜rev = W64 0⌝ ∗ indefCall err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
