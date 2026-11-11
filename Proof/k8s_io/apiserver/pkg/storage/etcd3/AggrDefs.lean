/-
Lean-first (no Rocq counterpart).

# The list error aggregators (stage 7e-2, #15 of `notes/k8s-7e-2-draft.md`, D2)

- `freshAggr ag`: the aggregator `ag` a factory just made (`&abortOnFirstError{}` or
  `&corruptObjErrAggregator{maxCount: n}`), nothing appended: its `Aggregate()` returns `nil` (once:
  the resource is the aggregator's state);
- `aggrFactoryOk f` (persistent): the store's `listErrAggrFactory` makes fresh aggregators.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A fresh aggregator (see the file header). -/
def freshAggr (ag : GoInterface) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜ag = GoInterface.ok ii⌝ ∗
    ∀ Φ : val → IProp GF, ▷ Φ #GoInterface.nil -∗
      WP (App (Val #(methods ii.ty go!"Aggregate" ii.v)) (Val #())) {{ Φ }})

/-- A factory of fresh aggregators (see the file header). -/
def aggrFactoryOk (f : GoFunc) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ ag, freshAggr ag -∗ Φ #ag) -∗
    WP (App (Val #f) (Val #())) {{ Φ }})

instance aggrFactoryOk_persistent (f : GoFunc) : Persistent (aggrFactoryOk (GF := GF) f) := by
  unfold aggrFactoryOk; infer_instance

end defs

end k8s
end EtcdGrove
end Perennial
