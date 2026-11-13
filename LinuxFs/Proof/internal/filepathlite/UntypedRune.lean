/-
**Go's semantics: operations on untyped rune constants** (WAL leaf specs, 2026-11-13). Lean-first.

`internal/filepathlite` on Unix compares and converts its constant `Separator = '/'` (an untyped
rune): `FromSlash`'s `if Separator == '/'` and `Base`'s `return string(Separator)`. Goose emits both
as run-time operations on the untyped constants (`GoOp GoEquals go.untypedRune`, `Convert
go.untypedRune go.string`) instead of folding them, and Perennial's semantics has no rule for
either (`UntypedIntSemantics` converts untyped integers to the integer types only; Perennial's
`strconv.lower` model says the same of a binary operation). In Go both are constant expressions,
evaluated at compile time (the language specification, "Constant expressions": a comparison of
untyped constants is an untyped boolean constant; "Conversions to and from a string type":
converting an integer to a string yields its UTF-8 encoding, a one-byte string for a rune below
`0x80`).

`UntypedRuneSemantics` states that they step: equality of untyped integers is equality of the
integers (as `IsStrictlyComparable` says of the typed ones), and `string(c)` of an untyped integer
is an uninterpreted string of it (`untypedRuneToString`), which is the one byte `c` for an ASCII
`c`. A **hypothesis class** on the semantics in use, like `UntypedIntToFloat64Semantics`
(`Proof/k8s_io/client_go/util/workqueue/UntypedIntToFloat.lean`), not an axiom: the results that
need it take it as an instance argument. The general fix (Goose folding constant expressions, or
the steps in Perennial's `UntypedIntSemantics`) is for Perennial (`notes/perennial-changes.md`).
-/
module

public import Perennial.Golang.Defn.Predeclared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **Equality and `string(c)` of untyped rune constants** (a hypothesis on the semantics in use,
see the file header). -/
class UntypedRuneSemantics [GooseExts] [GoLocalContext] [GoGlobalContext]
    [GoSemanticsFunctions] where
  /-- `a == b` of untyped integers: whether they are equal. -/
  eq_untyped_int : go.IsStrictlyComparable go.untypedInt Int
  /-- `string(c)` of the untyped integer `c`: uninterpreted but for ASCII. -/
  untypedRuneToString : Int → GoString
  untypedRuneToString_ascii (v : Int) : 0 ≤ v → v < 128 → untypedRuneToString v = [W8 v]
  convert_untyped_int_to_string (v : Int) :
    go.IsGoStepPureDetTagged under (Convert go.untypedInt go.string) #v
      (Val #(untypedRuneToString v))

attribute [instance] UntypedRuneSemantics.eq_untyped_int
  UntypedRuneSemantics.convert_untyped_int_to_string
export UntypedRuneSemantics (untypedRuneToString untypedRuneToString_ascii)

end EtcdGrove
end Perennial
