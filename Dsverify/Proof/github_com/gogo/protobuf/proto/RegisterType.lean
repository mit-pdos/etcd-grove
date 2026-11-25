/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `proto.RegisterType(x, name)` on an `x` that is not the `nil` interface (Go panics on it,
`reflect.Zero(nil)`), holding the program's package state: it writes `protoTypedNils` and
`revProtoTypes` and returns (a duplicate name is logged, not a panic).
Until dsv-fix4 a field of rabia's statement premise `github_com.gogo.protobuf.proto.Hyps`
(`Spec.lean`, whose header argues the preconditions from gogo/protobuf v1.3.2's
`proto/properties.go`); the statement is the field verbatim. `proto` is translated names only in
the part. Review: `notes/axiom-review/dsv-fix4/gogo-proto-register.md`.
-/
module

public import Dsverify.Proof.github_com.gogo.protobuf.proto.Spec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]

/-- **Trust-boundary axiom** (the file header). -/
axiom github_com.gogo.protobuf.proto.RegisterType.wp_proof :
  ∀ (σ : GMap GoString Bool) (x : GoInterface) (name : GoString),
    {{ ⌜x ≠ interface.nil⌝ ∗ (ownGoState σ : IProp GF) }}
      (App (App (Val #(functions github_com.gogo.protobuf.proto.RegisterType [])) (Val #x))
        (Val #name))
    {{ RET #(); ownGoState σ }}

end ax

end Perennial
