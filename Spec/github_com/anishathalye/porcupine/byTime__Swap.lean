/- Lean-first (no Rocq counterpart).

`byTime.Swap(i, j)` (checker.go), `i`, `j` in range: the two entries exchanged.
-/
module

public import Proof.github_com.anishathalye.porcupine.Entries

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev byTime.Swap.spec : Prop :=
  ∀ (sl : GoSlice) (es : List entry) (i j : w64) (a b : entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ sl ↦* es ∗
      ⌜0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧ es[sint.nat i]? = some a ∧ es[sint.nat j]? = some b⌝ }}
    (App (App (Val (sl @!! github_com.anishathalye.porcupine.byTime.ty @!! go!"Swap")) (Val #i))
      (Val #j))
  {{ RET #(); sl ↦* (es.set (sint.nat i) b).set (sint.nat j) a }}

end spec

end porcupine
end EtcdGrove
end Perennial
