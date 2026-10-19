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

- `wp_NewProph_typed`: `NewProph.impl #()` returns a fresh `p` with `typedProph p xs`, for some
  `xs` (the future);
- `wp_ResolveProph_typed`: `ResolveProph.impl #p #x` with `typedProph p xs` returns with
  `xs = x :: xs'` and `typedProph p xs'`;
- `typedProph_head`: the pure fact a commit uses: the next resolution is `xs.head?` (with
  `xs = []`, a later resolution is refuted, so whatever the commit chose holds vacuously).

## What the Go program calls

goose's `primitive` package has `NewProph() ProphId` and `ProphId.ResolveBool(b)`,
`ProphId.ResolveU64(x)`. Perennial's trusted model of it (`TrustedCode/.../primitive.lean`)
defines `NewProph.impl` and `ResolveProph.impl` (`λ p v, ResolveProph p v`), and `ProphId` as
`proph_id`, but its translation binds neither (the configuration's `trusted` list,
`Code/github_com/goose_lang/primitive.toml`, has `ProphId` without its methods and no
`NewProph`: "FIXME: add remaining functions"): `primitive.Assumptions` has no `FuncUnfold` of
`NewProph` and `ProphId.TypeAssumptions` no `MethodUnfold` of `ResolveBool`/`ResolveU64`. So
the specs here are of the trusted implementations; `wp_NewProph_call` is the Go call
`primitive.NewProph()` under the `FuncUnfold` instance the Perennial change will provide. The
Go program (`examples/linkv/linkv.go`) calls `primitive.NewProph()` and `p.ResolveBool(ok)`:
the outcome is a `Bool` (`true`: the call returned no error), all the commit needs (an `ok`
get's value is the one the server read at the commit). The Perennial change to propose (a general
one, on its own): bind `NewProph` (`FuncUnfold`) and `ProphId`'s `ResolveBool`/`ResolveU64`
(`MethodUnfold`, the receiver as `p`: `ResolveProph.impl`) in the configuration and the
trusted model.
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.Base

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
variable {τ : Type}

/-- **A typed prophecy**: `p` will be resolved with `#x` for the `x`s of `xs`, in order (and
then with something that is not a `τ`, or never again). -/
def typedProph (τ : Type) (p : proph_id) (xs : List τ) : IProp GF :=
  iprop(∃ pvs : List val, proph p pvs ∗ ⌜prophDecode τ pvs = xs⌝)

instance typedProph_timeless (p : proph_id) (xs : List τ) :
    Timeless (typedProph (GF := GF) τ p xs) := by
  unfold typedProph; infer_instance

/-- `NewProph.impl #()`: a fresh prophecy, of some future `xs`. -/
theorem wp_NewProph_typed :
    {{ (True : IProp GF) }} (App (Val github_com.goose_lang.primitive.NewProph.impl) (Val #()))
    {{ (p : proph_id) (xs : List τ), RET #p; typedProph τ p xs }} := by
  wp_start as _
  wp_apply wp_new_proph as %pvs %p Hp
  iapply HΦ
  iunfold typedProph
  iexists pvs
  iframe
  ipureintro; trivial

/-- `ResolveProph.impl #p #x`: the next of the prophesied values is `x`. -/
theorem wp_ResolveProph_typed (hinj : Function.Injective (intoVal (V := τ))) (p : proph_id)
    (xs : List τ) (x : τ) :
    {{ typedProph (GF := GF) τ p xs }}
      (App (App (Val github_com.goose_lang.primitive.ResolveProph.impl) (Val #p)) (Val #x))
    {{ (xs' : List τ), RET #(); ⌜xs = x :: xs'⌝ ∗ typedProph τ p xs' }} := by
  wp_start as Hp
  iunfold typedProph at Hp
  icases Hp with ⟨%pvs, Hp, %Hdec⟩
  wp_apply (wp_resolve_proph p pvs #x (GoGlobalContext.intoVal_not_panic x)) $$ Hp
    as %pvs' ⟨%Hpvs, Hp⟩
  iapply HΦ
  isplitr
  · ipureintro
    rw [← Hdec, Hpvs, prophDecode_cons hinj]
  iunfold typedProph
  iexists pvs'
  iframe
  ipureintro; trivial

/-- The Go call `primitive.NewProph()`, once Perennial binds it (see the file header). -/
theorem wp_NewProph_call
    [FuncUnfold github_com.goose_lang.primitive.NewProph [] github_com.goose_lang.primitive.NewProph.impl] :
    {{ (True : IProp GF) }} (App (Val (@! github_com.goose_lang.primitive.NewProph)) (Val #()))
    {{ (p : proph_id) (xs : List τ), RET #p; typedProph τ p xs }} := by
  wp_start as _
  wp_apply wp_new_proph as %pvs %p Hp
  iapply HΦ
  iunfold typedProph
  iexists pvs
  iframe
  ipureintro; trivial

/-- The outcome a commit learns: the next resolution, if it comes, is `xs.head?`. -/
theorem typedProph_head (xs : List τ) (x : τ) (xs' : List τ) (h : xs = x :: xs') :
    xs.head? = some x := by
  subst h; rfl

end specs

end linkv
end EtcdGrove
end Perennial
