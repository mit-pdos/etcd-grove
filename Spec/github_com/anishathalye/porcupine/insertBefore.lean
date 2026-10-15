/- Lean-first (no Rocq counterpart).

`insertBefore(n, mark)` (checker.go): links `n` before `mark` (if `mark` is not `nil`), and
returns `n`. Only the case where `mark` is first (its `prev` is `nil`) is specified: the only
one `makeLinkedEntries` and `checkSingle` use (they insert at the front of a list).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev insertBefore.spec : Prop :=
  ∀ (n : Loc) (vn : node) (mark : Loc) (vm : node),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ n ↦ vn ∗ (⌜mark = null⌝ ∨ mark ↦ vm ∗ ⌜vm.prev' = null⌝) }}
    (App (App (Val (@! github_com.anishathalye.porcupine.insertBefore)) (Val #n)) (Val #mark))
  {{ RET #n; (⌜mark = null⌝ ∗ n ↦ vn) ∨
      (n ↦ ({ vn with next' := mark } : node) ∗ mark ↦ ({ vm with prev' := n } : node)) }}

end spec

end porcupine
end EtcdGrove
end Perennial
