/-
`reflect.DeepEqual(nil, nil)` (names-only in Perennial: reflection): two nil `any` values are deeply
equal. A second spec of `reflect.DeepEqual` beside bbolt's (`DeepEqual.lean`, `spec_pgidSet`), in a
file of its own so that structured-merge-diff's proofs do not import bbolt (gen-link's `<fn>+<S>`
convention: `reflect_DeepEqual+Nil`, `reflect.DeepEqual.specNil`).

Its caller: `schema.StructField.Equals` (`schema/equals.go`: `reflect.DeepEqual(a.Default,
b.Default)`), reached on every merge and compare of structured-merge-diff through `TypeRef.Equals`
→ `Atom.Equals` → `Map.Equals`. The SMD driver's schema (`examples/k8s/smd`) has no field with a
default, so both arguments are the nil interface; a schema with defaults needs another case.

The trust boundary: an axiom, `Proof/reflect/DeepEqualNil.lean`. True of Go (`reflect/deepequal.go`,
go1.27):

    func DeepEqual(x, y any) bool {
        if x == nil || y == nil {
            return x == y
        }
        ...

With `x` and `y` both nil, it returns `x == y`, `true`, touching no memory. Lean-first
(2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.reflect.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev reflect.DeepEqual.specNil : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
    (App (App (Val #(functions _root_.Perennial.reflect.DeepEqual []))
      (Val #interface.nil)) (Val #interface.nil))
  {{ RET #true; True }}

end spec

end EtcdGrove
end Perennial
