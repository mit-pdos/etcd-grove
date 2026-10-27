/- Lean-first (no Rocq counterpart).

`byTime.Len()` (checker.go): `len(a)`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev byTime.Len.spec : Prop :=
  ∀ (sl : GoSlice) (es : List entry) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ sl ↦*{dq} es }}
    (App (Val (sl @!! github_com.anishathalye.porcupine.byTime.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 es.length); sl ↦*{dq} es }}

end spec

end porcupine
end EtcdGrove
end Perennial
