/-
**Go's semantics: `sync.Mutex{}`** (2026-10-26). Lean-first.

Perennial models `sync.Mutex` as a boolean (`TrustedCode/sync.lean`: underlying `go.bool`, the
zero value `false`, unlocked), and its semantics has composite-literal rules for structs, arrays,
slices, maps and pointers only (`Golang/Defn`); a composite literal at a named type steps as at
its underlying type (`composite_literal_underlying`). So `&sync.Mutex{}` (client-go's
`newQueue`: `sync.NewCond(&sync.Mutex{})`) reaches `CompositeLiteral go.bool (LiteralValueV [])`,
which has no step. In Go it is the zero `Mutex`, unlocked. `MutexLitSemantics` states that much
at the underlying type the model chose: the empty literal of `go.bool` (not Go syntax, only the
model's image of `sync.Mutex{}`) is its zero value `false`.

A **hypothesis class** on the semantics in use, like `EtcdGrove.Float64ToInt64Semantics`, not an
axiom: the results that need it take it as an instance argument (`etc/gen-link.py`'s
`SEM_PREMISES`). (The backend's `backend.wp_mutexLit`, `storage/backend/MutexLit.lean`, states the
same gap as an axiom of a WP, for every semantics; a model in which the literal does not step
makes that axiom false: `notes/STATUS.md`.) The general fix, an empty composite literal of a type
whose underlying type is not a struct being its zero value, is for Perennial
(`notes/perennial-changes.md`, "`sync.Mutex{}`").
-/
module

public import Perennial.Golang.Defn.PostLang

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **`sync.Mutex{}` is the zero `Mutex`** (a hypothesis on the semantics in use, see the file
header): the empty literal at the model's underlying type `go.bool` steps to `false`. -/
class MutexLitSemantics [FfiSyntax] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] : Prop where
  composite_literal_bool_empty :
    go.IsGoStepPureDetTagged under (CompositeLiteral go.bool) (LiteralValueV []) (Val #false)

attribute [instance] MutexLitSemantics.composite_literal_bool_empty

end EtcdGrove
end Perennial
