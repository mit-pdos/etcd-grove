/-
What the listers' paths through the store need (`tools/cache/listers.go`'s `ListAll`,
`ListAllByNamespace`; `k8s.io/client-go/listers`): a selector that selects everything, stores
without `nil` items, the namespace index's query object. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md`.

* `everySel sel`: `sel` is a selector `labels.MatchesNothing` says does not match nothing and whose
  `Empty()` is `true` (`labels.Everything()`'s `internalSelector{}`: the controller lists with it
  only). A premise: apimachinery's `labels` is names only (the boundary), and the client discharges
  it for `labels.Everything()`'s result.
* `noNil it`: no item is `nil` (the informers store only objects; a lister's type assertion on a
  `nil` item would panic).
* `qMeta ns`: the namespace index's query object, `&metav1.ObjectMeta{Namespace: ns}`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.CacheDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

/-- No item is `nil`. -/
def noNil [FfiSyntax] (it : Items) : Prop := ∀ k o, it !! k = some o → o ≠ interface.nil

/-- The namespace index's query object's contents: an `ObjectMeta` with only its namespace. -/
def qMeta [FfiSyntax] (ns : GoString) : k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta :=
  { (zero_val k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta) with Namespace' := ns }

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **A selector that selects everything** (persistent). -/
def everySel (sel : GoInterface) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜sel = interface.ok i⌝ ∗
    {{ True }} (App (Val (@! _root_.Perennial.k8s_io.apimachinery.pkg.labels.MatchesNothing))
      (Val #sel)) {{ RET #false; True }} ∗
    {{ True }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #())) {{ RET #true; True }})

instance everySel_persistent (sel : GoInterface) : Persistent (everySel (GF := GF) sel) := by
  unfold everySel; infer_instance

/-- The objects of `noNil` items meet the store's contract. -/
theorem okNil_noNil (OK : GoInterface → IProp GF) (it : Items) (k : GoString) (h : noNil it)
    (hk : k ∈ it) : okNil OK (objAt it k) ⊢ □ OK (objAt it k) := by
  rw [GMap.mem_iff] at hk
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hk
  have hn : objAt it k ≠ interface.nil := by unfold objAt; rw [ho]; exact h k o ho
  unfold okNil
  refine or_elim (pure_elim' fun h' => absurd h' hn) .rfl

end defs

end cache
end EtcdGrove
end Perennial
