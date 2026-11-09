/-
`proto.Equal(x, y)` (protobuf-go, assumed: `proto/equal.go`).

Users: raft's `ConfState` comparisons where they go through protobuf (3h's
`ConfState.Equivalent` sorts copies and compares fields; `EqualConfState` in the old specs), etcd's
`snapshot_merge`/`bootstrap` checks (2e).

Why true: `Equal` compares the two messages field by field (unknown fields byte-wise), reading
only; `Content` is the content up to `proto.Equal`, so the result is the contents' equality. etcd's
and raft's messages have no floating-point fields (no `NaN`).

Changes: from `specs-ref/.../proto/EqualConfState.lean`: any message type.

Margin: none.
-/
module

public import Spec.google_golang_org.protobuf.proto.Api

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

/-- `proto.Equal(x, y)` of two messages of one type: whether their contents are equal. -/
def Equal.spec : Prop :=
  ∀ (t : go.GoType) (p q : Loc) (dp dq : DFrac) (c d : Content),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ msgAt t p dp c ∗ msgAt t q dq d ∗ ⌜depth c < depthMax ∧ depth d < depthMax⌝ }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Equal)) (Val #(msgVal t p))) (Val #(msgVal t q)))
  {{ (b : Bool), RET #b; msgAt t p dp c ∗ msgAt t q dq d ∗ ⌜b = true ↔ c = d⌝ }}

end spec

end Proto
end EtcdGrove
end Perennial
