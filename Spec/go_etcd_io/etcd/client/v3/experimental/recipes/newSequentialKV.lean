/-
`recipe.newSequentialKV(kv, prefix, val)` (`key.go`): read the last key under `prefix`
(`WithLastKey()`), take the next sequence number `n`, and put `__prefix` and `prefix/<n, 16 digits>`
in a transaction guarded by `__prefix` not having been written since the read; retried on a failed
guard.

**Users**: `PriorityQueue.Enqueue`. Internal.

**Proof sketch**: a loop carrying the caller's update. `kv.Get(TODO(), prefix, WithLastKey()...)`
(`KV.GetTriple`, an update made of `etcdPeek`: a read leaves the state unchanged) gives the last key
and the header's revision `R`; `strings.Split`, `fmt.Sscanf("%d")` (Perennial) the number, an error
returned as is (`err ≠ nil`, update unfired); `fmt.Sprintf("%s/%016d")` the key `seqKey prefix n`;
then the transaction `seqPutReq (seqBase prefix) (seqKey prefix n) val (R + 1)` (W0's `Txn`
contract) with an update built from the caller's: a failed comparison aborts it and the call recurses,
any other answer commits it. `R + 1 ≤ σ.kv.rev + 1` at the transaction (`etcdLb_reach` from the read's
`etcdLb`, the revision only grows).

**Changes**: old spec over the recipes' client invariant (the prefix written by the recipes only) and
a sequence certificate; now the caller's update, with the transaction's request.

**Margin**: `n` is one more than the sequence number of the last key under `prefix` at revision `R`
(or `0`); the spec says only that the key is `seqKey prefix n` for some `n` (the parse is
`fmt.Sscanf`'s). An `int` overflow of `n` (a last key numbered `2^63 - 1`) gives a negative `n`,
which `padDec` covers.
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

/-- **`newSequentialKV(kv, prefix, val)`**: `__prefix` and a key `prefix/<n>` put by one guarded transaction the caller's update linearizes (attempts whose guard failed change nothing). -/
def newSequentialKV.spec : Prop :=
  ∀ (kv : GoInterface) (γ : Cluster) (who : Principal) (pre val : GoString)
    (Q : State → State → Int → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ kvAt kv γ who ∗ etcdPeek γ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (n bound : Int) (res : Resp),
             ⌜bound ≤ σ.kv.rev + 1 ∧
              Step who (seqPutReq (seqBase pre) (seqKey pre n) val bound) σ σ' res ∧
              ¬ txnCmpFailed res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' n res }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newSequentialKV)) (Val #kv))
      (Val #pre)) (Val #val))
  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (∃ σ σ' n res, Q σ σ' n res ∗
        ((⌜txnSucceeded res ∧ err = GoInterface.nil⌝ ∗
           rkOwn rk γ who { live := true, key := seqKey pre n, rev := W64 σ'.kv.rev, val := val }) ∨
         ⌜∃ e, res = .err e ∧ err = errVal e ∧ rk = null⌝)) ∨
      ⌜err ≠ GoInterface.nil ∧ rk = null⌝ }}

end spec

end Recipes
end EtcdGrove
end Perennial
