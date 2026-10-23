/-
`b.Bytes()` of the buffer at `b`: a slice of its bytes (it aliases the buffer, which is given up).

The trust boundary: an axiom, `Proof/bytes/Buffer__Bytes.lean` (`bytes.Buffer`'s methods are not translated; `Proof/bytes/Buffer.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.bytes.Buffer
public import Perennial.Proof.bytes.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI bufferM

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bytes.Assumptions]

/-- See the file header. -/
abbrev bytes.Buffer.Bytes.spec : Prop :=
  ∀ (b : Loc) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bytes ∗ ownBuffer b bs }}
    (App (Val #(methods (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) go!"Bytes" #b))
      (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* bs }}

end spec

end EtcdGrove
end Perennial
