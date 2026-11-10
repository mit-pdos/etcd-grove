/-
`reflect.Kind` values compare as `uint`s (Go: `type Kind uint`, `reflect/type.go`): `==` on two
`Kind`s is the equality of their numbers. Perennial's `reflect` axiomatizes the type `Kind` (its
underlying type is an axiom), so `v.Kind() != reflect.Slice` (`store.GetList`, `store.go:780`;
`reflect.Value.Kind.spec` returns `#(W64 23)`) has no semantics without it.

Not an axiom: a premise (`?`, pending) of the results that reach `store.GetList` until
etcd-grove-81 decides between a trust-boundary fact here and a Perennial translation of `Kind`
(`notes/perennial-changes.md`, "`reflect.Kind` is an axiomatized type"). Lean-first.
-/
module

public import Proof.reflect.Values
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

include hG in
/-- See the file header. -/
abbrev reflect.KindCompare.spec : Prop :=
  go.IsStrictlyComparable _root_.Perennial.reflect.Kind.underlying w64

end spec

end EtcdGrove
end Perennial
