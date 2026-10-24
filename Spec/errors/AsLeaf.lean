/-
`errors.As(err, target)` of an `errors.New` error whose type is outside the target's type set: the
trust boundary (rafthttp stage 4: the pipeline handler's `errors.As(err, &writerToResponse)` on
`Process`'s error). Lean-first.
-/
module

public import Perennial.Proof.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.As(err, &v)` with `err` an `errors.New` error (a `*errorString` with no `As` or
`Unwrap` method: `isLeafError`) whose type is not in the type set of the target's element type
`T`: `false`, the target unchanged. Perennial's `errors.As.spec` (an axiom: `As` uses reflection,
not translated) allows any result. -/
abbrev errors.AsLeaf.spec : Prop :=
  ∀ (x l : Loc) {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.GoType}
    [IntoValTyped (GF := GF) T' T] (v : T'),
    _root_.Perennial.errors.AsTarget T →
    _root_.Perennial.errors.isLeafError
      ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ →
    go.typeSetContains (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) T = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v }}
      (App (App (Val (@! _root_.Perennial.errors.As))
        (Val #(interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x)))
        (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #false; l ↦ v }}

end spec

end EtcdGrove
end Perennial
