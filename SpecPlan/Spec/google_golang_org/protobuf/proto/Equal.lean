/-
`proto.Equal(x, y)` (protobuf-go, assumed: `proto/equal.go`).

Users: raft's `ConfState` comparisons where they go through protobuf (3h's
`ConfState.Equivalent` sorts copies and compares fields; `EqualConfState` in the old specs), etcd's
`snapshot_merge`/`bootstrap` checks (2e).

Why true: `Equal` compares the two messages field by field (unknown fields byte-wise), reading
only, over the populated fields (an empty `bytes` field and a `nil` one are both unset): the
result is the equality of the wire views `norm c`, `norm d`, except that a `NaN` float field is
unequal to itself (so `Equal(m, m)` may be `false`): the converse needs `noFloats t`, true of every
etcd and raft message.

Changes: from `specs-ref/.../proto/EqualConfState.lean`: any message type.
verify-round (A6 F2 and second tier): over `norm` (the content is no longer up to `Equal`); the
`NaN` case: `b = true` only implies equality, the converse under `noFloats t`.

Margin: none.
-/
module

public import SpecPlan.Spec.google_golang_org.protobuf.proto.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Proto

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.protobuf.proto.Assumptions]

/-- `proto.Equal(x, y)` of two messages of one type: `true` only if their wire views are equal;
for a type without floating-point fields, exactly then. -/
def Equal.spec : Prop :=
  ∀ (t : go.GoType) (p q : Loc) (dp dq : DFrac) (c d : Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgAt t p dp c ∗ msgAt t q dq d ∗ ⌜depth c < depthMax ∧ depth d < depthMax⌝ }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Equal)) (Val #(msgVal t p))) (Val #(msgVal t q)))
  {{ (b : Bool), RET #b; msgAt t p dp c ∗ msgAt t q dq d ∗
      ⌜(b = true → norm c = norm d) ∧ (noFloats t → norm c = norm d → b = true)⌝ }}

end spec

end Proto
end EtcdGrove
end Perennial
