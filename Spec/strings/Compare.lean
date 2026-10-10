/-
`strings.Compare(a, b)` (Go's standard library, `bytealg.CompareString`: assembly). Perennial has no
model of it: the trust boundary (an axiom, `Proof/strings/Compare.lean`), for
`client/v3/leasing`'s `inRange`. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.strings

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- What `strings.Compare(a, b)` returns: `0` if `a = b`, `-1` if `a` is before `b` in Go's string
order (bytewise, `GoStringLt`), `+1` otherwise. -/
def stringsCompareResult (a b : GoString) : w64 :=
  if a = b then W64 0 else if go.GoStringLt a b then W64 (-1) else W64 1

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `strings.Compare(a, b)`: `stringsCompareResult a b`. -/
abbrev strings.Compare.spec : Prop :=
  ∀ (a b : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (App (Val #(functions _root_.Perennial.strings.Compare [])) (Val #a)) (Val #b))
  {{ RET #(stringsCompareResult a b); True }}

end spec

end EtcdGrove
end Perennial
