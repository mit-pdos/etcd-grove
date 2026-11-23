/-
`reflect.Kind` values compare as `uint`s (Go: `type Kind uint`, `reflect/type.go`): `==` on two
`Kind`s is the equality of their numbers, so that `v.Kind() != reflect.Slice` (`store.GetList`,
`store.go:780`; `reflect.Value.Kind.spec` returns `#(W64 23)`) compares words. Perennial translates
`Kind` (`Kind := w64`, `Kind.underlying := go.uint`, reducible; Perennial `3eae9cd1f`), so this is
`uint`'s comparison, proved from `go.Semantics` (`Proof/reflect/KindCompare.lean`; until 2026-11-23
an axiom, when Perennial axiomatized `Kind`). Lean-first.
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
