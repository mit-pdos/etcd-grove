/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `proto.RegisterEnum("message.MsgType", MsgType_name, MsgType_value)`, rabia's `message.pb.go`'s
first `init`: called inside `message`'s initialization, once (it consumes the points-to of
`message`'s package variable `MsgType_value`, which only `message`'s initializer holds), holding the
program's package state (initializers run one at a time); it writes `enumValueMaps` and returns (a
second registration of the name, which panics, is not covered).
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
axiom github_com.gogo.protobuf.proto.RegisterEnum.wp_proofMsgType :
  ∀ (σ : GMap GoString Bool) (nameMap valueMap : Loc),
    {{ (ownGoState σ : IProp GF) ∗
        globalAddr rabia.internal.message.MsgType_value ↦ valueMap }}
      (App (App (App (Val #(functions github_com.gogo.protobuf.proto.RegisterEnum []))
        (Val #(go!"message.MsgType"))) (Val #nameMap)) (Val #valueMap))
    {{ RET #(); ownGoState σ }}

end ax

end Perennial
