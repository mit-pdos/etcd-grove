/-
Lean-first (no Rocq counterpart).

# linkv: typed prophecy variables (2026-10-19)

D20, part (c): the `lintest` instance's `apply` closure creates a prophecy before its call to
etcd's client and resolves it with the call's outcome after it returns, so that the call's
linearization point (the server's apply, or its read) knows the output it will return. GooseLang
has prophecy variables (`NewProph`, `ResolveProph`; `wp_new_proph`, `wp_resolve_proph`,
`GooseLang/Lifting.lean`) over untyped values: `proph p pvs`, `pvs` the values `p` will be
resolved with. This file types them, as Iris's `typed_proph` does
(`iris/heap_lang/lib/typed_proph.v`): `typedProph p xs` (`xs : List τ`, for any `τ` whose
`intoVal` is injective, e.g. `Bool`, `w64`) holds the decoding of `pvs` up to its first value
that is not some `#x`; resolving with `#x` takes `x` off the front.

- `wp_NewProph_typed`: `primitive.NewProph()` returns a fresh `p` with `typedProph p xs`, for
  some `xs` (the future);
- `wp_ResolveBool_typed`: `p.ResolveBool(b)` (the receiver a value) with `typedProph Bool p xs`
  returns with `xs = b :: xs'` and `typedProph Bool p xs'`;
- `wp_ptr_ResolveBool_typed`: the same through a pointer to the `ProphId` (`l.ResolveBool(b)`,
  `l ↦{dq} p`), the call the Go program makes;
- `typedProph_head`: the pure fact a commit uses: the next resolution is `xs.head?` (with
  `xs = []`, a later resolution is refuted, so whatever the commit chose holds vacuously).

The wrappers are lemmas over Perennial's specs of the calls (hypotheses `wp_NewProph`,
`wp_ResolveBool`: `Perennial/Spec/github_com/goose_lang/primitive/`, linked in Perennial's
`Perennial/Proof/github_com/goose_lang/primitive/Link.lean`), so that `Apply`'s proof, which
takes those specs as its callee specs, applies them with them.

## What the Go program calls

goose's `primitive` package has `NewProph() ProphId` and `(ProphId) ResolveBool(b)`,
`(ProphId) ResolveU64(x)` (no-op stubs in Go). Perennial (since `ca6988bb0`/`e81f4a6ce`) binds
them: `primitive.Assumptions.NewProph_unfold` (`NewProph.impl`), `ProphId.TypeAssumptions`'s
`ResolveBool_unfold`/`ResolveU64_unfold` (`ProphId.ResolveBool.impl`: `ResolveProph p b`), and
the generated pointer-receiver wrappers `ptr_ResolveBool_unfold`/`ptr_ResolveU64_unfold` (load
the `ProphId`, then call the value method), with the specs `primitive.wp_NewProph` and
`ProphId.wp_ResolveBool`/`wp_ResolveU64` over the untyped `proph p pvs`. The Go program
(`examples/linkv/linkv.go`, `Apply`) calls `p := primitive.NewProph()`, keeps `p` in a local
variable (a heap cell, in the translation) and calls `p.ResolveBool(!out.Err)` on it: Go takes
the variable's address, so the translation calls the pointer-receiver method
(`MethodResolve (PointerType ProphId.ty) "ResolveBool"` on the cell), whose spec is
`wp_ptr_ResolveBool_typed`. (Its proof needs `go.NotInterface go.prophId` to step the value
method's `MethodResolve ProphId.ty`, which Perennial does not provide: its `NotInterface`
instances are per constructor and do not unfold the predeclared types' definitions, `go.prophId`
as `go.int`; `notInterface_prophId` states it here. The general fix, instances for the
predeclared types or making them reducible, is to propose to Perennial on its own.) The outcome
is a `Bool` (`true`: the call returned no error), all the commit needs (an `ok` get's value is
the one the server read at the commit). `ResolveU64` has no wrapper here: the program does not
call it.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.NewProph
public import Perennial.Spec.github_com.goose_lang.primitive.ProphId__ResolveBool

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section decode
variable [FfiSyntax] [GoGlobalContext]
variable (τ : Type)

open Classical in
/-- The prophesied values as `τ`s, up to the first value that is not some `#x`. -/
def prophDecode : List val → List τ
  | [] => []
  | v :: vs => if h : ∃ x : τ, #x = v then Classical.choose h :: prophDecode vs else []

variable {τ}

theorem prophDecode_cons (hinj : Function.Injective (intoVal (V := τ))) (x : τ) (vs : List val) :
    prophDecode τ (#x :: vs) = x :: prophDecode τ vs := by
  have h : ∃ y : τ, #y = #x := ⟨x, rfl⟩
  simp only [prophDecode, h, dite_true]
  rw [hinj (Classical.choose_spec h)]

end decode

section specs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]
variable {τ : Type}

/-- **A typed prophecy**: `p` will be resolved with `#x` for the `x`s of `xs`, in order (and
then with something that is not a `τ`, or never again). -/
def typedProph (τ : Type) (p : proph_id) (xs : List τ) : IProp GF :=
  iprop(∃ pvs : List val, proph p pvs ∗ ⌜prophDecode τ pvs = xs⌝)

instance typedProph_timeless (p : proph_id) (xs : List τ) :
    Timeless (typedProph (GF := GF) τ p xs) := by
  unfold typedProph; infer_instance

/-- `go.prophId` (`ProphId`'s underlying type) is not an interface: the premise of stepping
`MethodResolve ProphId.ty m #p` (`go_method_resolve_step`). Perennial proves `go.NotInterface` per
constructor of `go.GoType` and does not see through the (not reducible) definitions of the
predeclared types (`go.prophId`, `go.int`, ...), so the instance is stated here (a Perennial gap:
see the file header). -/
instance notInterface_prophId : go.NotInterface go.prophId := ⟨by unfold go.prophId; trivial⟩

/-- `primitive.NewProph()`: a fresh prophecy, of some future `xs`. -/
theorem wp_NewProph_typed
    (wp_NewProph : github_com.goose_lang.primitive.NewProph.spec (GF := GF) (hG := hG)) :
    {{ (True : IProp GF) }} (App (Val (@! github_com.goose_lang.primitive.NewProph)) (Val #()))
    {{ (p : proph_id) (xs : List τ), RET #p; typedProph τ p xs }} := by
  wp_start_folded as _
  wp_apply wp_NewProph as %pvs %p Hp
  iapply HΦ
  iunfold typedProph
  iexists pvs
  iframe
  ipureintro; trivial

/-- The decoding after a resolution with `#x`: `x` comes off the front. -/
theorem typedProph_resolve (hinj : Function.Injective (intoVal (V := τ)))
    (xs : List τ) (x : τ) (pvs pvs' : List val) (hdec : prophDecode τ pvs = xs)
    (hpvs : pvs = #x :: pvs') : xs = x :: prophDecode τ pvs' := by
  rw [← hdec, hpvs, prophDecode_cons hinj]

/-- `p.ResolveBool(b)`: the next of the prophesied values is `b`. -/
theorem wp_ResolveBool_typed
    (wp_ResolveBool : github_com.goose_lang.primitive.ProphId.ResolveBool.spec (GF := GF) (hG := hG))
    (p : proph_id) (xs : List Bool) (b : Bool) :
    {{ typedProph (GF := GF) Bool p xs }}
      (App (Val (p @!! github_com.goose_lang.primitive.ProphId.ty @!! go!"ResolveBool")) (Val #b))
    {{ (xs' : List Bool), RET #(); ⌜xs = b :: xs'⌝ ∗ typedProph Bool p xs' }} := by
  wp_start_folded as Hp
  iunfold typedProph at Hp
  icases Hp with ⟨%pvs, Hp, %Hdec⟩
  wp_apply wp_ResolveBool p pvs b $$ Hp as %pvs' ⟨%Hpvs, Hp⟩
  iapply HΦ
  isplitr
  · ipureintro
    exact typedProph_resolve go.intoVal_inj xs b pvs pvs' Hdec Hpvs
  iunfold typedProph
  iexists pvs'
  iframe
  ipureintro; trivial

/-- `l.ResolveBool(b)` on a `*ProphId` `l` holding `p` (the Go program's call, see the file
header): the next of the prophesied values is `b`. -/
theorem wp_ptr_ResolveBool_typed
    (wp_ResolveBool : github_com.goose_lang.primitive.ProphId.ResolveBool.spec (GF := GF) (hG := hG))
    (l : Loc) (dq : DFrac) (p : proph_id) (xs : List Bool) (b : Bool) :
    {{ typedPointsto (GF := GF) l p dq ∗ typedProph Bool p xs }}
      (App (Val (l @!! go.GoType.PointerType github_com.goose_lang.primitive.ProphId.ty @!!
        go!"ResolveBool")) (Val #b))
    {{ (xs' : List Bool), RET #(); ⌜xs = b :: xs'⌝ ∗ typedPointsto l p dq ∗
        typedProph Bool p xs' }} := by
  wp_start as ⟨Hl, Hp⟩
  wp_auto
  wp_apply wp_ResolveBool_typed wp_ResolveBool p xs b $$ Hp as %xs' ⟨%Hxs, Hp⟩
  iapply HΦ
  iframe
  ipureintro; exact Hxs

/-- The outcome a commit learns: the next resolution, if it comes, is `xs.head?`. -/
theorem typedProph_head (xs : List τ) (x : τ) (xs' : List τ) (h : xs = x :: xs') :
    xs.head? = some x := by
  subst h; rfl

end specs

end linkv
end EtcdGrove
end Perennial
