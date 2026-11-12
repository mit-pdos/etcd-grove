/- Lean-first (no Rocq counterpart).

`b.hash()` (bitset.go): some hash of the words (the cache is sound for any hash, so nothing is
said of it).
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
abbrev bitset.hash.spec : Prop :=
  ∀ (b : GoSlice) (ws : List w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ b ↦*{dq} ws }}
    (App (Val (b @!! bitset.ty @!! go!"hash")) (Val #()))
  {{ (h : w64), RET #h; b ↦*{dq} ws }}

end spec

end porcupine
end EtcdGrove
end Perennial
