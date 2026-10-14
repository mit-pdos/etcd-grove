/- Lean-first (no Rocq counterpart).

`makeLinkedEntries(entries)` (checker.go): the entries' nodes, linked in order (`linked`, the
first one's `prev` `nil`), each call's `match` its return's node; it returns the first node
(`nil` if there are none).
-/
module

public import Proof.github_com.anishathalye.porcupine.Linked

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
abbrev makeLinkedEntries.spec : Prop :=
  ∀ (hsl : GoSlice) (es : List entry) (dq : DFrac) (h : List (Theory.Op OpV)),
  EntriesFor h es → (h.length : Int) < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ hsl ↦*{dq} es }}
    (App (Val (@! github_com.anishathalye.porcupine.makeLinkedEntries)) (Val #hsl))
  {{ (root : Loc), RET #root; hsl ↦*{dq} es ∗
      ∃ loc : Entry → Loc, linked loc (valOf h) null (es.map entryOf) ∗
        ⌜root = headLoc loc (es.map entryOf) ∧ ∀ e ∈ es.map entryOf, loc e ≠ null⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
