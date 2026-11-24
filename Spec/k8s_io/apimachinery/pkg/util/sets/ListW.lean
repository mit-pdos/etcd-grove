/-
`List(s)` of a set of decision words (`Set[authorizer.Decision]`): a new slice of its items.
Lean-first; the second spec of `List` (the first, `List.lean`, is for strings), for the
conditional authorizer's failure messages. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.sets.Defs
public import Code.k8s_io.apiserver.pkg.authorization.authorizer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI k8s_io.apimachinery.pkg.util.sets

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- See the file header. The set has at most `2^62` items (`slices.Sort`'s bound, as in
`List'.spec`). -/
abbrev List'.specW : Prop :=
  ∀ (m : Loc) (dq : DFrac) (s : GMap w64 Elem), GMap.size s ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗ m ↦${dq} s }}
    (App (Val #(functions List'' [_root_.Perennial.k8s_io.apiserver.pkg.authorization.authorizer.Decision.ty]))
      (Val #m))
  {{ (sl : GoSlice) (ks : List w64), RET #sl; m ↦${dq} s ∗ sl ↦* ks ∗
      ⌜∀ k, k ∈ ks ↔ (s !! k).isSome⌝ }}

end spec

end sets
end EtcdGrove
end Perennial
