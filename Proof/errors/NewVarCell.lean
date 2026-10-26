/-
**`errors.New`'s message cell** (D19k, 2026-10-18): what tells two `errors.New` variables apart.

`errors.New(msg)` allocates a fresh `errorString{s: msg}` and nothing writes its `s` field again,
so the field holds `msg` for good (`errStrCell`; Perennial's `context.wp_New_errorString` persists
the cell in its proof and drops it from its postcondition: `wp_New_errorString_cell` here is the
same proof keeping it, a candidate Perennial change). Two variables whose cells hold different
messages hold different pointers (`errVarApart_of`): two `↦□` at one cell agree. The packages'
facts carry the cells of the variables a proof must tell apart (`errVarCell`): the server's
`applyEntryNormal` needs the backend's errors told apart from `ErrNoSpace` (the apply package's
`applyErrVars`), so that `errors.Is(ar.Err, ErrNoSpace)` is `false` (D19k).

`errorsNewVarInitC init X msg`: `errorsNewVarInit`'s statement with the cell, the form of the
`errorsNewVarsInit` axioms (`etcdserver/errors`, bbolt's `errors`): still what Go's
`var X = errors.New(msg)` does.
-/
module

public import Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The `errorString` at `x` holds `msg`** (persistent): its `s` field, which only
`errors.New` writes. -/
def errStrCell (x : Loc) (msg : GoString) : IProp GF :=
  iprop(x.[_root_.Perennial.errors.errorString, go!"s"] ↦□ msg)

instance errStrCell_persistent (x : Loc) (msg : GoString) :
    Persistent (errStrCell (GF := GF) x msg) := by
  unfold errStrCell; infer_instance

/-- `errorsNewVarInit` with the message cell: `init` runs `X = errors.New(msg)`, `X`'s cell
holding a fresh `*errorString` whose `Error()` returns `msg` and whose `s` field holds `msg`. -/
abbrev errorsNewVarInitC (init : val) (X msg : GoString) : Prop :=
  {{ (True : IProp GF) }} (App (Val init) (Val #()))
  {{ RET #(); ∃ x : Loc,
      globalAddr X ↦ interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x ∗
      (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
          go!"Error" #x)) (Val #())) {{ Φ }}) ∗
      errStrCell x msg }}

/-- **`X` holds an `errors.New(msg)` error with its cell** (persistent; a package fact). -/
def errVarCell (X msg : GoString) : IProp GF :=
  iprop(∃ x : Loc,
    globalAddr X ↦□ interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x ∗
    errStrCell x msg)

instance errVarCell_persistent (X msg : GoString) : Persistent (errVarCell (GF := GF) X msg) := by
  unfold errVarCell; infer_instance

/-- `errVarCell` of each `(X, msg)` of a list. -/
def errVarCells : List (GoString × GoString) → IProp GF
  | [] => iprop(True)
  | (X, m) :: l => iprop(errVarCell X m ∗ errVarCells l)

instance errVarCells_persistent (l : List (GoString × GoString)) :
    Persistent (errVarCells (GF := GF) l) := by
  induction l with
  | nil => unfold errVarCells; infer_instance
  | cons p l ih => obtain ⟨X, m⟩ := p; unfold errVarCells; infer_instance

theorem errVarCells_mem {l : List (GoString × GoString)} {X m : GoString} (h : (X, m) ∈ l) :
    errVarCells (GF := GF) l ⊢ errVarCell X m := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    obtain ⟨Y, n⟩ := p
    unfold errVarCells
    rcases List.mem_cons.1 h with h | h
    · cases h; exact sep_elim_left
    · exact sep_elim_right.trans (ih h)

/-- **The variables `g` and `h` hold different errors** (persistent). -/
def errVarApart (g h : GoString) : IProp GF :=
  iprop(∃ e1 e2 : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e1 ∗
    globalAddr h ↦□ GoInterface.ok e2 ∗ ⌜e1 ≠ e2⌝)

instance errVarApart_persistent (g h : GoString) : Persistent (errVarApart (GF := GF) g h) := by
  unfold errVarApart; infer_instance

/-- Cells of different messages are different cells. -/
theorem errStrCell_ne (x y : Loc) (m m' : GoString) (hm : m ≠ m') :
    errStrCell (GF := GF) x m ⊢ errStrCell y m' -∗ ⌜x ≠ y⌝ := by
  unfold errStrCell
  iintro #H1 #H2
  by_cases hxy : x = y
  · subst hxy
    icombine H1 H2 gives %h
    exact absurd h hm
  · ipureintro; exact hxy

/-- **Two `errors.New` variables of different messages hold different errors.** -/
theorem errVarApart_of (g h m m' : GoString) (hm : m ≠ m') :
    errVarCell (GF := GF) g m ⊢ errVarCell h m' -∗ errVarApart g h := by
  unfold errVarCell errVarApart
  iintro ⟨%x, #Hg, #Hx⟩ ⟨%y, #Hh, #Hy⟩
  ihave %Hne := errStrCell_ne x y m m' hm $$ Hx Hy
  iexists _, _
  iframe Hg Hh
  ipureintro
  intro he
  apply Hne
  injection he with _ hv
  exact go.intoVal_inj (V := Loc) hv

/-- **An `errors.New` variable apart from each of a list's** (the auth plan's E3i): its message
differs from all of theirs. -/
theorem errVarApart_cells (g m : GoString) (l : List (GoString × GoString))
    (hne : ∀ p ∈ l, p.2 ≠ m) :
    errVarCell (GF := GF) g m ⊢ errVarCells l -∗
      □ ∀ X : GoString, ⌜X ∈ l.map Prod.fst⌝ -∗ errVarApart g X := by
  iintro #Hg #Hl !> %X %hX
  obtain ⟨⟨X', m'⟩, hmem, rfl⟩ := List.mem_map.1 hX
  ihave #HX := errVarCells_mem (GF := GF) hmem $$ Hl
  iapply errVarApart_of g X' m m' (fun h => hne _ hmem h.symm) $$ Hg HX

end defs

section wp
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [errors_sem : _root_.Perennial.errors.Assumptions]

/-- **`errors.New(msg)` with its cell**: Perennial's `context.wp_New_errorString` (the same
proof), keeping the `s` field it persists (a candidate Perennial change, D19k). -/
theorem wp_New_errorString_cell (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x);
        (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
            go!"Error" #x)) (Val #())) {{ Φ }}) ∗ errStrCell x msg }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  isplitl
  · imodintro
    iintro %Φ HΦ
    rw [method_unfold]
    wp_auto
    iexact HΦ
  · unfold errStrCell
    iexact s

end wp

end EtcdGrove
end Perennial
