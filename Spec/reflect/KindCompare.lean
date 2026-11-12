/-
`reflect.Kind` values compare as `uint`s (Go: `type Kind uint`, `reflect/type.go`): `==` on two
`Kind`s is the equality of their numbers. Perennial's `reflect` axiomatizes the type `Kind` (its
underlying type is an axiom), so `v.Kind() != reflect.Slice` (`store.GetList`, `store.go:780`;
`reflect.Value.Kind.spec` returns `#(W64 23)`) has no semantics without it.

Faithful: Go declares `type Kind uint` (`reflect/type.go`), so `==` on `Kind`s is `uint` equality,
always defined, and the 64-bit `uint` of the pinned `amd64` toolchain is a `w64`; the translation
compares with `GoOp GoEquals reflect.Kind.ty` against `#(W64 23)`
(`examples/k8s7e2attack/attack_test.go` `TestKindIsUint`). The trust boundary: an axiom,
`Proof/reflect/KindCompare.lean` (decided by etcd-grove-81 after the review of 2026-11-10, where it was
a pending premise; the general fix, a Perennial translation of `Kind`, is proposed in
`notes/perennial-changes.md`, "`reflect.Kind` is an axiomatized type"). Lean-first.
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
