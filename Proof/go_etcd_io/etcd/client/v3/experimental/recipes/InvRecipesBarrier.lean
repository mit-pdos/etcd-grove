/-
`client/v3/experimental/recipes`' barrier (`barrier.go`): the vocabulary of its specs. Lean-first
(no Rocq counterpart); see `decisions.md`, "Recipes: the client contracts reused, the queue's
claim, two prefixes as one".

**The barrier** (`isBarrier b client key`, persistent): its fields, read-only (`NewBarrier` writes
them once: the client, `context.TODO()`, the key), and the client's contracts at the prefix `key`
(`isEtcdRecipesClient client key`: the barrier touches its key alone, a range under itself).
`Hold` creates the key (or finds it there: `ErrKeyExists`), `Release` deletes it, and `Wait`
returns `nil` only once the key was absent at some revision at or after its get's
(`etcdAbsent`): at the get's, or at a delete event's.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **A `*Barrier`** `b` on the key `key` (persistent): its fields, read-only (the client, the
context `context.TODO()`, the key), and the client's contracts at the prefix `key`
(`isEtcdRecipesClient`). -/
def isBarrier (b client : Loc) (key : GoString) : IProp GF :=
  iprop(structFieldRef Barrier go!"client" b ↦□ client ∗
    structFieldRef Barrier go!"ctx" b ↦□ GoInterface.ok todoCtxVal ∗
    structFieldRef Barrier go!"key" b ↦□ key ∗ isEtcdRecipesClient client key)

instance isBarrier_persistent (b client : Loc) (key : GoString) :
    Persistent (isBarrier (GF := GF) b client key) := by
  unfold isBarrier; infer_instance

end defs

end recipes
end EtcdGrove
end Perennial
