/- Lean-first (no Rocq counterpart).

`bitsetIndex(pos)` (bitset.go): the word and the bit of position `pos`.
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
abbrev bitsetIndex.spec : Prop :=
  ∀ (pos : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine }}
    (App (Val (@! github_com.anishathalye.porcupine.bitsetIndex)) (Val #pos))
  {{ RET (PairV #(pos / W64 64) #(pos % W64 64)); True }}

end spec

end porcupine
end EtcdGrove
end Perennial
