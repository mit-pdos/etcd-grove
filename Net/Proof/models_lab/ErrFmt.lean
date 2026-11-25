/-
`errFmt e` (dsv-fix6, `notes/dsv-fix6.md`, craq): what `fmt` does with the error `e` under any verb,
`%#v` included, is call its `Error()` (under a method verb, `errAny`'s WP) and nothing else, reading
only persistent memory. Go's `fmt` (`print.go`, `handleMethods`, `printValue`) calls an operand's
`Format` under every verb and `GoString` under `%#v`; under `%#v` it dereferences a top-level pointer
to a struct and visits the struct's fields (depth 1), calling the same methods of an exported field's
value and, for an interface field, of its dynamic value (depth 2), where a pointer is printed as an
address (nothing read; under the verbs `v s q x X d` only: other verbs reprint it through `badVerb`, dereferencing it, so a `Printf` using `errFmt` asks for those verbs, craq's `FmtVerbsOk`) and a struct's fields are visited again. So `errFmt e` asks: `e`'s type has
neither `Format` nor `GoString` (it implements neither `fmt.Formatter` nor `fmt.GoStringer`), and `e`
is one of the shapes the net world's errors take, with the memory `%#v` reads persistent:
* `ServerError` (net/rpc's, a string type: printed as a quoted string);
* `*errors.errorString` `x` with `x.s ↦□ s` (one unexported string field);
* `*pbcodec.Error`/`*jsoncodec.Error` `x` with `x ↦□ v` (one exported string field);
* `*net.OpError` `pe` with `pe ↦□ v` (`Op`, `Net` strings; `Source`, `Addr`, `Err` interfaces whose
  values are `errLeaf`: `nil`, or a value with neither method of a pointer type, of `poll`'s
  `errNetClosing` (an empty struct) or of `textproto.ProtocolError` (a string type); or, for `Err`, the value of `poll.ErrDeadlineExceeded`, a
  timeout's `Err`: Go's `&DeadlineExceededError{}`, a pointer without either method, but `poll`'s
  package fact (Perennial's `Proof/internal/poll/Base.lean`) says only that the variable holds some
  error, so the variable's points-to stands for it: `notes/perennial-changes.md`, "net's errors and
  `errors.Is`").
`errPlain err` is `errAny err` with this fact: what Net's own specs (not the premises or axioms that
say `errAny` of a real library's error) return, so that a log call's argument condition holds of it.
-/
module

public import Net.Proof.models_lab.Errors
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Code.internal.poll
public import Net.GeneratedProof.net
public import Net.GeneratedProof.net.rpc
public import Net.GeneratedProof.net.textproto
public import Net.GeneratedProof.models_lab.pbcodec
public import Net.GeneratedProof.models_lab.jsoncodec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace models_lab

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `t` implements neither `fmt.Formatter` nor `fmt.GoStringer`: `fmt` calls no `Format` or
`GoString` of a value of type `t`. -/
def NoFmtMeth (t : go.GoType) : Prop :=
  go.typeSetContains t fmt.Formatter.ty = false ∧ go.typeSetContains t fmt.GoStringer.ty = false

/-- An interface value `fmt` reaches at depth ≥ 2 under `%#v` (see the file header): `nil`, or of a
type without `Format`/`GoString` that is a pointer type (printed as an address), `poll`'s
`errNetClosing` (an empty struct) or `textproto.ProtocolError` (a string type, printed as a quoted
string: `http.ReadResponse`'s malformed header error). -/
def errLeaf (i : GoInterface) : Prop :=
  i = interface.nil ∨ ∃ ii : GoInterfaceOk, i = interface.ok ii ∧ NoFmtMeth ii.ty ∧
    ((∃ t, ii.ty = go.GoType.PointerType t) ∨ ii.ty = internal.poll.errNetClosing.ty ∨
      ii.ty = net.textproto.ProtocolError.ty)

end pure

section types
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem noFmt_errorString [errors.Assumptions] [fmt.Assumptions] : NoFmtMeth (go.GoType.PointerType errors.errorString.ty) :=
  ⟨by go_type_set, by go_type_set⟩

theorem noFmt_serverError [net.rpc.Assumptions] [fmt.Assumptions] : NoFmtMeth net.rpc.ServerError.ty :=
  ⟨by go_type_set, by go_type_set⟩

theorem noFmt_opError [net.Assumptions] [fmt.Assumptions] : NoFmtMeth (go.GoType.PointerType net.OpError.ty) :=
  ⟨by go_type_set, by go_type_set⟩

theorem noFmt_pbcodecError [pbcodec.Assumptions] [fmt.Assumptions] : NoFmtMeth (go.GoType.PointerType pbcodec.Error.ty) :=
  ⟨by go_type_set, by go_type_set⟩

theorem noFmt_TCPAddr [net.Assumptions] [fmt.Assumptions] : NoFmtMeth (go.GoType.PointerType net.TCPAddr.ty) :=
  ⟨by go_type_set, by go_type_set⟩

theorem noFmt_syscallError [os.Assumptions] [fmt.Assumptions] : NoFmtMeth (go.GoType.PointerType os.SyscallError.ty) :=
  ⟨by go_type_set, by go_type_set⟩

theorem noFmt_errNetClosing [internal.poll.Assumptions] [fmt.Assumptions] : NoFmtMeth internal.poll.errNetClosing.ty :=
  ⟨by go_type_set, by go_type_set⟩

theorem noFmt_protocolError [net.textproto.Assumptions] [fmt.Assumptions] : NoFmtMeth net.textproto.ProtocolError.ty :=
  ⟨by go_type_set, by go_type_set⟩

theorem errLeaf_nil : errLeaf interface.nil := Or.inl rfl

/-- A pointer of a type without `Format`/`GoString` is `errLeaf`. -/
theorem errLeaf_ptr (t : go.GoType) (v : val) (h : NoFmtMeth (go.GoType.PointerType t)) :
    errLeaf (interface.mkOk (go.GoType.PointerType t) v) :=
  Or.inr ⟨⟨go.GoType.PointerType t, v⟩, rfl, h, Or.inl ⟨t, rfl⟩⟩

theorem noFmt_jsoncodecError [jsoncodec.Assumptions] [fmt.Assumptions] : NoFmtMeth (go.GoType.PointerType jsoncodec.Error.ty) :=
  ⟨by go_type_set, by go_type_set⟩

end types

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def errFmt (e : GoInterfaceOk) : IProp GF :=
  iprop(⌜NoFmtMeth e.ty⌝ ∗
    (⌜e.ty = net.rpc.ServerError.ty⌝ ∨
     (∃ (x : Loc) (s : GoString), ⌜e = ⟨go.GoType.PointerType errors.errorString.ty, #x⟩⌝ ∗
        x.[errors.errorString, go!"s"] ↦□ s) ∨
     (∃ (x : Loc) (v : pbcodec.Error), ⌜e = ⟨go.GoType.PointerType pbcodec.Error.ty, #x⟩⌝ ∗
        x ↦□ v) ∨
     (∃ (x : Loc) (v : jsoncodec.Error), ⌜e = ⟨go.GoType.PointerType jsoncodec.Error.ty, #x⟩⌝ ∗
        x ↦□ v) ∨
     (∃ (pe : Loc) (v : net.OpError), ⌜e = ⟨go.GoType.PointerType net.OpError.ty, #pe⟩⌝ ∗
        ⌜errLeaf v.Source' ∧ errLeaf v.Addr'⌝ ∗
        (⌜errLeaf v.Err'⌝ ∨ globalAddr internal.poll.ErrDeadlineExceeded ↦□ v.Err') ∗ pe ↦□ v)))

instance errFmt_persistent (e : GoInterfaceOk) : Persistent (errFmt (GF := GF) e) := by
  unfold errFmt; infer_instance

/-- `errAny err` and `fmt` formats it calling only its `Error()` (`errFmt`). -/
def errPlain (err : GoInterface) : IProp GF :=
  iprop(errAny err ∗ ∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ errFmt e)

instance errPlain_persistent (err : GoInterface) : Persistent (errPlain (GF := GF) err) := by
  unfold errPlain; infer_instance

theorem errPlain_errAny (err : GoInterface) : errPlain (GF := GF) err ⊢ errAny err := by
  unfold errPlain
  iintro ⟨#H, -⟩
  iexact H

end defs

end models_lab
end Perennial
