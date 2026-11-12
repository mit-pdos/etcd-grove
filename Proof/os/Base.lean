/-
Shared definitions of the specs of `os`'s trusted models (`TrustedCode/os.lean`, this repository's
`os`, project `bboltfs`): the typed points-to of the model's `file` and `fileStat`, and the
resource of an open `*os.File` (`ownFile`) and of the `fileStat` its `Stat` returns
(`ownFileStat`).

The model's `file` and `fileStat` are trusted types (`Code/os.toml`); goose emits no field-access
assumptions for them (`file.TypeAssumptions` has no `get_fd`/`set_fd`, unlike `File`'s
`get_file`), so `TrustedCode/os.lean` states them by hand (`file.FieldAssumptions`,
`fileStat.FieldAssumptions`), and their `IntoValTyped`, which a `GoAlloc` of one needs (in
`OpenFile` and `Stat`), takes them as instance hypotheses. Their fields are owned one by one
(`structFieldRef os.file go!"fd" inner ↦ fd`), which is all that loads and stores need.
-/
module

public import GeneratedProof.os
public import Proof.syscall.Base
public import GooseLang.Ext.OsFs.Truncate

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace os

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : os.Assumptions]

theorem file_ty_eq : os.model.file = os.file.ty := by
  unfold os.file.ty; rfl

theorem File_ty_eq : os.model.File = os.File.ty := by
  unfold os.File.ty; rfl

theorem fileStat_ty_eq : os.model.fileStat = os.fileStat.ty := by
  unfold os.fileStat.ty; rfl

/-! The typed points-to of the model's `file` and `fileStat`, as goose emits it for a translated
struct; their `IntoValTyped` needs the struct-field facts of `TrustedCode/os.lean`
(`file.FieldAssumptions`, `fileStat.FieldAssumptions`), which goose cannot emit for a trusted
layout. -/

instance file_fields_unfold :
    EqualsUnfold [go.field_decl.FieldDecl go!"fd" go.int, go.field_decl.FieldDecl go!"name" go.string]
      [go.field_decl.FieldDecl go!"fd" go.int, go.field_decl.FieldDecl go!"name" go.string] :=
  ⟨rfl⟩

instance fileStat_fields_unfold :
    EqualsUnfold [go.field_decl.FieldDecl go!"size" go.int64]
      [go.field_decl.FieldDecl go!"size" go.int64] :=
  ⟨rfl⟩

noncomputable instance file_typed_pointsto : TypedPointsto (GF := GF) os.file where
  typedPointstoDef l v dq := iprop(
    "fd" ∷ typedPointsto (structFieldRef os.file go!"fd" l) v.fd' dq ∗
    "name" ∷ typedPointsto (structFieldRef os.file go!"name" l) v.name' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

noncomputable instance file_into_val_typed [os.file.FieldAssumptions] :
    IntoValTypedUnderlying (GF := GF) os.file os.file.underlying := by
  solve_into_val_typed_struct

noncomputable instance fileStat_typed_pointsto : TypedPointsto (GF := GF) os.fileStat where
  typedPointstoDef l v dq := iprop(
    "size" ∷ typedPointsto (structFieldRef os.fileStat go!"size" l) v.size' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

noncomputable instance fileStat_into_val_typed [os.fileStat.FieldAssumptions] :
    IntoValTypedUnderlying (GF := GF) os.fileStat os.fileStat.underlying := by
  solve_into_val_typed_struct

include sem package_sem' in
/-- The `*os.File` `f` is open on the fd `fd`, named `name`: `f` points to a `File` whose inner
`file` holds the fd (a fraction `dq` of it: `Close` writes it) and the name. -/
def ownFile (f : Loc) (fd : w64) (name : GoString) (dq : DFrac) : IProp GF :=
  iprop(∃ inner : Loc, f ↦□ (os.File.mk inner) ∗
    structFieldRef os.file go!"fd" inner ↦{dq} fd ∗
    structFieldRef os.file go!"name" inner ↦□ name)

include sem package_sem' in
/-- The `fileStat` at `fs` (what `(*File).Stat` returns, as a `FileInfo`) holds the size `sz`. -/
def ownFileStat (fs : Loc) (sz : w64) : IProp GF :=
  iprop(structFieldRef os.fileStat go!"size" fs ↦□ sz)

/-- One of the ranges `rs` of bytes held (each `(off, dq, xs)`: `osBytes p off dq xs`) says that
byte `i` of the file is `b`. -/
def heldByte (rs : List (Nat × DFrac × List (w8 × Bool))) (i : Nat) (b : w8) : Prop :=
  ∃ r ∈ rs, r.1 ≤ i ∧ (r.2.2[i - r.1]?).map Prod.fst = some b

variable [syscall.Assumptions] in
/-- `f.wrapErr(op, Errno(e))` (`model.wrapErrno`) for the file whose inner `file` is `inner`: a
fresh `*PathError` as an `error`. -/
theorem wp_wrapErrno (op : GoString) (inner : Loc) (name : GoString) (e : w64)
    (Φ : val → IProp GF) :
    structFieldRef os.file go!"name" inner ↦□ name -∗
      (∀ pe : Loc, Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val os.model.wrapErrno) (Val #op)) (Val #inner)) (Val #e)) {{ Φ }} := by
  iintro #Hn HΦ
  unfold os.model.wrapErrno os.model.pathError
  rw [file_ty_eq]
  wp_auto
  wp_apply wp_errno
  iapply HΦ

end def_
end os

end Perennial
