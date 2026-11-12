/- Lean-first (no Rocq counterpart).

`b.equal(b2)` (bitset.go): whether the two bitsets have the same words.
-/
module

public import Proof.github_com.anishathalye.porcupine.Bitset

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
abbrev bitset.equal.spec : Prop :=
  ∀ (b : GoSlice) (ws : List w64) (dq : DFrac) (b2 : GoSlice) (ws2 : List w64) (dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ b ↦*{dq} ws ∗ b2 ↦*{dq2} ws2 }}
    (App (Val (b @!! bitset.ty @!! go!"equal")) (Val #b2))
  {{ RET #(decide (ws = ws2)); b ↦*{dq} ws ∗ b2 ↦*{dq2} ws2 }}

end spec

end porcupine
end EtcdGrove
end Perennial
