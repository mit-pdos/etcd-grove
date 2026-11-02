/- Lean-first (no Rocq counterpart).

`(*client).unlift(top, serialized)` (dag.go, PR #46): the head moves back, and the bitset loses
`top.opId`. The panic (`top` of another client) is unreachable: the frames record their client.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Search

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev client.unlift.spec : Prop :=
  ∀ (cp : Loc) (cv : client) (top : stackEntry) (lin_ptr : Loc) (lsl : GoSlice) (ws : List w64),
  top.clientId' = cv.id' → 0 ≤ sint.Z top.opId' → uint.nat top.opId' / 64 < ws.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ cp ↦ cv ∗ lin_ptr ↦ lsl ∗ lsl ↦* ws }}
    (App (App (Val (cp @!! go.GoType.PointerType client.ty @!! go!"unlift")) (Val #top))
      (Val #lin_ptr))
  {{ RET #(); cp ↦ { cv with head' := cv.head' - W64 1 } ∗ lin_ptr ↦ lsl ∗
      lsl ↦* bsClear ws top.opId' }}

end spec

end porcupine
end EtcdGrove
end Perennial
