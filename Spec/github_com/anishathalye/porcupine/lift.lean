/- Lean-first (no Rocq counterpart).

`lift(entry)` (checker.go): unlinks the node of a call `⟨false, y⟩` of the list and the node of
its return (later in the list), leaving them with their neighbours ("dancing links"): the list
when `y` is lifted too (`nodesOwn`, `layout`).
-/
module

public import Proof.github_com.anishathalye.porcupine.Nodes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev lift.spec : Prop :=
  ∀ (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface) (es : List Entry) (B : List Nat)
    (p q y : Nat),
  es.Nodup → (rem es B)[p]? = some ⟨false, y⟩ → p < q → (rem es B)[q]? = some ⟨true, y⟩ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ nodesOwn hd loc val es B }}
    (App (Val (@! github_com.anishathalye.porcupine.lift)) (Val #(loc ⟨false, y⟩)))
  {{ RET #(); nodesOwn hd loc val es (y :: B) }}

end spec

end porcupine
end EtcdGrove
end Perennial
