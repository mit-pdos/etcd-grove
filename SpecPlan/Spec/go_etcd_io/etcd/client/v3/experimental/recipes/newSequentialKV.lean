/-
`recipe.newSequentialKV(kv, prefix, val)` (`key.go`): read the last key under `prefix`
(`WithLastKey()`), take the next sequence number `n`, and put `__prefix` and `prefix/<n, 16 digits>`
in a transaction guarded by `__prefix` not having been written since the read; retried on a failed
guard.

**Users**: `PriorityQueue.Enqueue`. Internal.

**Proof sketch**: a loop carrying the caller's update. `kv.Get(TODO(), prefix, WithLastKey()...)`
(`KV.GetTriple`, an update made of `etcdPeek`, whose commit gives `etcdLb γ σg`) gives the last key
in key order (`lastKeyIn`: prefix, sorted by key descending, limit 1) and the header's revision
`R = σg.kv.rev`; `strings.Split` (Perennial) its `lastField`; `Fmt.Sscanf_d.spec` (this batch's
trust boundary, `SpecPlan/Spec/fmt/Sscanf.lean`) the number: a scanning error is returned as is
(`Fmt.scanErr`: `recipeErrOk`; update unfired); `n` the number plus one, so `seqNext (σg's store)
prefix n` (an `int` overflow needs a field of `2^63 - 1`, which `seqNext` excludes);
`fmt.Sprintf("%s/%016d")` the key `seqKey prefix n`; then the transaction `seqPutReq (seqBase
prefix) (seqKey prefix n) val (R + 1)` (`R + 1 < 2^63`: `etcdLb_revFits`) with an update built from
the caller's: a failed comparison aborts it and the call recurses, any other answer commits it, with
`R ≤ σ.kv.rev` (`etcdLb_reach`) and `σ.kv.storeAt R` = `σg`'s store (the history only grows).

**Changes**: old spec over the recipes' client invariant (the prefix written by the recipes only) and
a sequence certificate; now the caller's update, with the transaction's request and its read: `R`
and `seqNext (σ.kv.storeAt R) prefix n` (review 1f-completeness-1, C-2: for a prefix whose keys are
`seqKey`s and whose writers bump `__prefix`, the new key is past every key present at `R`, and none
was added since, the guard holding).

**Margin**: for a last field that is not a decimal number below `2^63 - 1`, `n` is whatever `Sscanf`
stored, plus one.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

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
    (Q : State → State → Nat → Int → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ kvAt kv γ who ∗ etcdPeek γ ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (R : Nat) (n : Int) (res : Resp),
             ⌜R ≤ σ.kv.rev ∧ seqNext (σ.kv.storeAt R) pre n ∧
              Step who (seqPutReq (seqBase pre) (seqKey pre n) val (R + 1)) σ σ' res ∧
              ¬ txnCmpFailed res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' R n res }> }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newSequentialKV)) (Val #kv))
      (Val #pre)) (Val #val))
  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (∃ σ σ' R n res, Q σ σ' R n res ∗
        ((⌜txnSucceeded res ∧ err = GoInterface.nil⌝ ∗
           rkOwn rk γ who { live := true, key := seqKey pre n, rev := W64 σ'.kv.rev, val := val }) ∨
         ⌜∃ e, res = .err e ∧ err = errVal e ∧ rk = null⌝)) ∨
      (⌜err ≠ GoInterface.nil ∧ rk = null⌝ ∗ recipeErrOk err) }}

end spec

end Recipes
end EtcdGrove
end Perennial
