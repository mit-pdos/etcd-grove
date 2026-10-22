/-
`b.Write(p)` on the buffer at `b`: it appends `p`'s bytes and answers their number and no error.

The trust boundary: an axiom, `Proof/bytes/Buffer__Write.lean` (`bytes.Buffer`'s methods are not translated; `Proof/bytes/Buffer.lean`). Lean-first (no Rocq counterpart).
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
abbrev bytes.Buffer.Write.spec : Prop :=
  ∀ (b : Loc) (bs : List w8) (sl : GoSlice) (dq : DFrac) (d : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bytes ∗ ownBuffer b bs ∗ sl ↦*{dq} d }}
    (App (Val #(methods (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) go!"Write" #b))
      (Val #sl))
  {{ RET (PairV #(W64 (d.length : Int)) #GoInterface.nil);
      ownBuffer b (bs ++ d) ∗ sl ↦*{dq} d }}

end spec

end EtcdGrove
end Perennial
