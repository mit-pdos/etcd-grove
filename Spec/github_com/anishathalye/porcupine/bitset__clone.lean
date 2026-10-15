/- Lean-first (no Rocq counterpart).

`b.clone()` (bitset.go): a fresh copy of the words.
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
abbrev bitset.clone.spec : Prop :=
  ∀ (b : GoSlice) (ws : List w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗ b ↦*{dq} ws }}
    (App (Val (b @!! bitset.ty @!! go!"clone")) (Val #()))
  {{ (b' : GoSlice), RET #b'; b ↦*{dq} ws ∗ b' ↦* ws }}

end spec

end porcupine
end EtcdGrove
end Perennial
