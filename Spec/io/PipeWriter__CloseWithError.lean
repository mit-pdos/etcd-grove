/-
`pw.CloseWithError(err)` (`io.PipeWriter`'s; names only in Perennial; D22 S-h, 2026-10-20): the
pipe's writer end closed, the reader's later reads returning `err` (`io.EOF` for a nil `err`). The
trust boundary (an axiom in `Proof/io/PipeWriter__CloseWithError.lean`); see `Spec/io/Pipe.lean`.
-/
module

public import Proof.io.Defs
public import Perennial.Code.io

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `pw.CloseWithError(err)` of the writer end promised to `Φ` with the hand-over `T`, at the bytes
`bs` written: given `Φ bs` if `err` is nil (the reader's complete stream is then `bs`), the writer
closed (its predicate consumed: nothing is written after), and `T` handed over if a `Write` has
returned (`c`: the reader had it, see `Proof/io/Defs.lean`); it returns nil (`closeWrite` always
does). -/
abbrev io.PipeWriter.CloseWithError.spec : Prop :=
  ∀ (pw : Loc) (Φ : List w8 → Prop) (T : IProp GF) (c : Bool) (bs : List w8) (err : GoInterface),
  {{ io.pipeW (GF := GF) pw Φ T c bs ∗ ⌜err = GoInterface.nil → Φ bs⌝ }}
    (App (Val (pw @!! go.GoType.PointerType _root_.Perennial.io.PipeWriter.ty @!!
      go!"CloseWithError")) (Val #err))
  {{ RET #GoInterface.nil; if c then T else True }}

end spec

end EtcdGrove
end Perennial
