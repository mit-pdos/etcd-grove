/-
`(*Barrier).Wait()` (`barrier.go`): `Get(key)`; absent: return; else wait for a delete of the key from
the next revision (`WaitEvents`).

**Users**: `T/v3_barrier_test.go:59` (released only after `Release`), `:105` (an absent key: at
once), `T/v3_closed_watch_test.go:181` (a closed client: an error, the fixed
`issues/recipes-barrier-wait-closed-watch.md`). Snippet: `recipes/barrier.go` (`ReqWaitAfterRelease`,
`ReqWaitAbsent`).

**Proof sketch**: `KV.GetTriple` (`isClient_KV`, `kvAt_methods`) with a persistent update made of
`etcdPeek`: at its firing, `etcdState γ σg`, `etcdLb_reach` from `etcdLb γ σ0` gives `Reach σ0 σg`,
`etcdState_lb` the `etcdLb γ σg` its `Q` keeps; the reply's model is the range's answer at `σg`'s
store (`kvStep`'s linearizable range). No key: `r = σg.kv.rev`. Else `WaitEvents.spec` from
`σg.kv.rev + 1` for `[DELETE]` (`etcdState_revFits`, with one revision to spare, for the `int64`
addition: W0's `etcdLb_revFits`): the first delete of `key` after `σg`, at a revision
`r > σg.kv.rev ≥ σ0.kv.rev` of the history (`goneAt`'s second case).

**Changes**: old spec required the recipes' client invariant and stated absence (`etcdAbsent`); now
any client, and the fact is `goneAt` (absent, or deleted at `r`: a revision may delete and re-put the
key in sibling nested transactions, which no store fact rules out).

**Margin**: errors (the `Get`'s, the watch's) say nothing more.
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

/-- **`b.Wait()`**: `nil` only if the barrier key was gone (absent, or deleted) at some revision after `σ0` (a state the caller knew before the call). -/
def Barrier.Wait.spec : Prop :=
  ∀ (b c : Loc) (γ : Cluster) (who : Principal) (key : GoString) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ barrierAt b c γ who key ∗ etcdPeek γ ∗ etcdLb γ σ0 }}
    (App (Val (b @!! go.GoType.PointerType Barrier.ty @!! go!"Wait")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err ≠ GoInterface.nil⌝ ∗ recipeErrOk err) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (σ : State) (r : Nat), etcdLb γ σ ∗
        ⌜σ0.kv.rev ≤ r ∧ r ≤ σ.kv.rev ∧ goneAt σ.kv key r⌝) }}

end spec

end Recipes
end EtcdGrove
end Perennial
