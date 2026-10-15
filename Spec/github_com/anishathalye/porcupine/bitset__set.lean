/- Lean-first (no Rocq counterpart).

`b.set(pos)` (bitset.go): sets bit `pos` in place (`bsSet`), returning `b`. The word must
exist (`pos / 64 < len(b)`), or the indexing panics.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev bitset.set.spec : Prop :=
  ∀ (b : GoSlice) (ws : List w64) (pos : w64),
  uint.nat pos / 64 < ws.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ b ↦* ws }}
    (App (Val (b @!! bitset.ty @!! go!"set")) (Val #pos))
  {{ RET #b; b ↦* bsSet ws pos }}

end spec

end porcupine
end EtcdGrove
end Perennial
