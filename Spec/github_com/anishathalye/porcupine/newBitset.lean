/- Lean-first (no Rocq counterpart).

`newBitset(bits)` (bitset.go): a bitset of `bits` bits, all clear (`bsChunks bits` zero words).
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
abbrev newBitset.spec : Prop :=
  ∀ (bits : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine }}
    (App (Val (@! github_com.anishathalye.porcupine.newBitset)) (Val #bits))
  {{ (b : GoSlice), RET #b; b ↦* List.replicate (bsChunks (uint.nat bits)) (W64 0) }}

end spec

end porcupine
end EtcdGrove
end Perennial
