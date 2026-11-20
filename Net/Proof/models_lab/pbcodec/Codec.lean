/-
What a generated protobuf codec (`models/protobuf/pbgen.py`: `pbMarshal`, `pbUnmarshal`, over `pbcodec`) is
proved to meet, per program: the obligations a model of `google.golang.org/protobuf` takes of the
codec registered with it (phase 5 of notes/dsverify-net-port-plan.md). Ported from dsverify-lab's
`Harness/Proof/grpc/Pb.lean` (`348a866`), the statements kept; what changed is in the plan note,
phase 5 item 1.

**The codec** (`PbCodec`, a type class: the program's, whose instance its proof chooses):
* `marshal m Ψ`: the deposit for `Marshal(m)` (what the program's `pbMarshal` needs, e.g. the
  ownership of the message `m` points to), whose result the call returns: `Ψ (some bs)` with the
  encoding `bs` in the returned slice and a nil error, or `Ψ none` with a non-nil error;
* `unmarshal bs m Ψ`: the deposit for `Unmarshal(data, m)` of `data`'s bytes `bs`, whose result
  `Ψ ok` (`ok` iff the error is nil) the call returns.
`marshalOk fm`, `unmarshalOk fu` say the functions `fm`, `fu` meet them (persistent; the program's
proof proves them of its generated functions). A codec's error is some error (`errAny`): the
generated codec's are `*pbcodec.Error`s (`Error_errAny`).
-/
module

public import Net.Proof.models_lab.Errors
public import Net.Proof.models_lab.pbcodec.Base
public import Net.Spec.models_lab.pbcodec.Error__Error

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.pbcodec

/-- The program's protobuf codec, as the specs see it (see the file header). -/
class PbCodec [GooseExts] (GF : BundledGFunctors) where
  marshal : GoInterface → (Option (List w8) → IProp GF) → IProp GF
  unmarshal : List w8 → GoInterface → (Bool → IProp GF) → IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [PbCodec GF]

/-- `Marshal`'s function `fm` meets `PbCodec.marshal`. -/
def marshalOk (fm : GoFunc) : IProp GF :=
  iprop(□ ∀ (m : GoInterface) (Ψ : Option (List w8) → IProp GF) (Φ : val → IProp GF),
    PbCodec.marshal m Ψ -∗
    ▷ (∀ (s : GoSlice) (err : GoInterface),
        ((⌜err = interface.nil⌝ ∗ ∃ bs, s ↦* bs ∗ Ψ (some bs)) ∨
          (⌜err ≠ interface.nil⌝ ∗ errAny err ∗ Ψ none)) -∗ Φ (PairV #s #err)) -∗
    WP (App (Val #fm) (Val #m)) {{ Φ }})

/-- `Unmarshal`'s function `fu` meets `PbCodec.unmarshal`. -/
def unmarshalOk (fu : GoFunc) : IProp GF :=
  iprop(□ ∀ (data : GoSlice) (dq : DFrac) (bs : List w8) (m : GoInterface)
      (Ψ : Bool → IProp GF) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗ PbCodec.unmarshal bs m Ψ -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else errAny err) -∗ Φ #err) -∗
    WP (App (App (Val #fu) (Val #data)) (Val #m)) {{ Φ }})

instance marshalOk_persistent (fm : GoFunc) : Persistent (marshalOk (GF := GF) fm) := by
  unfold marshalOk; infer_instance
instance unmarshalOk_persistent (fu : GoFunc) : Persistent (unmarshalOk (GF := GF) fu) := by
  unfold unmarshalOk; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.pbcodec.Assumptions]

/-- `*pbcodec.Error` is in the type set of `error` (its method `Error() string`). -/
theorem Error_is_error :
    go.typeSetContains (go.GoType.PointerType Error.ty) go.error = true := by
  go_type_set

/-- A `*pbcodec.Error` the program keeps for good (`↦□`, as the generated codec's errors may be
kept) is some error. -/
theorem Error_errAny (wp_Error : Error.Error.spec (GF := GF) (hG := hG)) (e : Loc) (v : Error) :
    (e ↦□ v : IProp GF) ⊢ errAny (interface.mkOk (go.GoType.PointerType Error.ty) #e) := by
  iintro #He
  unfold errAny
  iexists (interface.mk (go.GoType.PointerType Error.ty) #e)
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact Error_is_error
  imodintro
  iintro %Φ Hk
  wp_apply (wp_Error e v)
  · iexact He
  iapply Hk

end laws

end models_lab.pbcodec
end Perennial
