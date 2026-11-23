/-
Ported from dsverify-lab examples/gryff/proof/Harness/Proof/github_com/goose_lang/primitive/Proph.lean
(run gryff-bump-1; notes/dsv-gryff.md), in namespace `Perennial.gryff.lib`; Perennial `7b2259a12` still
lacks `go.NotInterface go.prophId`.

Prophecy variables in a target (kits/gryff-net: a fork may insert them as marked ghost code):
Perennial's `github.com/goose-lang/primitive` (`NewProph`, `ProphId.ResolveBool`,
`ProphId.ResolveU64`; `Perennial/Proof/github_com/goose_lang/primitive/Link.lean`: `wp_NewProph`,
`ProphId.wp_ResolveU64`, ...) gives their specs, and the distributed statement's adequacy covers
them (`Harness/SafeDist.lean`: Perennial's `goose_dist_adequacy` keeps the prophecy map in the
global state; a node's prophecy steps are GooseLang's `NewProph` and `ResolveProph`). What the
pinned Perennial lacks for a call of a `ProphId` method on a value (`p.ResolveU64(x)` where `p`
is a variable or a struct field, as goose translates it, `MethodResolve ProphId.ty ...`):
`go.NotInterface go.prophId` (`ProphId`'s underlying type is the predeclared `go.prophId`, a
named type, but a `def` instance search does not unfold), which the step of `MethodResolve`
needs. Proved here (no axiom), with the spec of the call through a pointer (a struct field or a
local variable holding the `ProphId`).

Example: `kits/gryff-net/dev/proph` (a Go program with a prophecy, translated, and `SafeDist`
proved for it).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- `go.prophId` (a named predeclared type) is not an interface type: the instance search
cannot see through its `def`. -/
instance gryff.lib.notInterface_prophId : go.NotInterface go.prophId := ⟨by unfold go.prophId; trivial⟩

namespace gryff.lib
open github_com.goose_lang.primitive (ProphId)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- `l.ResolveU64(x)` for `l` a pointer to a `ProphId` (Go's automatic `(*l).ResolveU64(x)`,
as goose translates `s.p.ResolveU64(x)` for a struct field `p` or a variable `p`). -/
theorem ProphId.wp_ResolveU64_ptr (l : Loc) (dq : DFrac) (p : ProphId) (pvs : List val)
    (x : w64) :
    {{ (l ↦{dq} p ∗ proph p pvs : IProp GF) }}
      (App (Val (l @!! go.PointerType ProphId.ty @!! go!"ResolveU64")) (Val #x))
    {{ (pvs' : List val), RET #(); l ↦{dq} p ∗ ⌜pvs = #x :: pvs'⌝ ∗ proph p pvs' }} := by
  wp_start as ⟨Hl, Hp⟩
  wp_auto
  wp_apply github_com.goose_lang.primitive.ProphId.wp_ResolveU64 $$ Hp as %pvs' ⟨%Hr, Hp⟩
  iapply HΦ
  iframe
  ipureintro; exact Hr

/-- `l.ResolveBool(b)` for `l` a pointer to a `ProphId`. -/
theorem ProphId.wp_ResolveBool_ptr (l : Loc) (dq : DFrac) (p : ProphId) (pvs : List val)
    (b : Bool) :
    {{ (l ↦{dq} p ∗ proph p pvs : IProp GF) }}
      (App (Val (l @!! go.PointerType ProphId.ty @!! go!"ResolveBool")) (Val #b))
    {{ (pvs' : List val), RET #(); l ↦{dq} p ∗ ⌜pvs = #b :: pvs'⌝ ∗ proph p pvs' }} := by
  wp_start as ⟨Hl, Hp⟩
  wp_auto
  wp_apply github_com.goose_lang.primitive.ProphId.wp_ResolveBool $$ Hp as %pvs' ⟨%Hr, Hp⟩
  iapply HΦ
  iframe
  ipureintro; exact Hr

end spec

end gryff.lib

end Perennial
